import LeanVIPR

/-!
# `viprcheck` — re-check a VIPR result certificate

Usage:

* `viprcheck <certificate.vipr>`
* `viprcheck --native-mode <full|slice> <certificate.vipr>`
* `viprcheck --kernel-mode <full|reconstruct> <certificate.vipr>
    [--proof-dir <dir>]`

The default mode parses a VIPR v1.0 file and runs the array-backed `checkVipr` as
compiled code, covering `SOL`, `{ sol }`, final objective-bound checking, and
infeasibility results. It trusts the Lean compiler and runtime, and says so in its
verdict line. SCIP is not invoked; the certificate file is the input.

`--kernel-mode` instead emits the parsed certificate as Lean data and asks Lean's
kernel to reduce the checker over it, which yields a machine-checked theorem and
the axioms it rests on. It costs minutes per certificate and only small ones
finish, so it is the proof-of-concept for the trusted path rather than the way to
check a solver run. `RTP infeas` retains the optional reconstruction optimization.

Native replay is split across `VIPRCHECK_TASKS` tasks (default 8, `1` for
sequential). The count cannot change a verdict:
`LeanVIPR.Thm.Checker.checkViprPar_eq` holds for every task count.

The checker is proved sound directly against the declarative VIPR proof system.

The generated theorem currently certifies the emitted certificate AST. Binding that
AST to the exact source bytes remains a frontend parser/runtime trust boundary.
-/

open LeanVIPR.Parser LeanVIPR.Semantics LeanVIPR.Semantics.Lower
open LeanVIPR.Checker LeanVIPR.Parser.Vipr

inductive KernelMode where
  | full
  | reconstruct

def parseKernelMode? : String → Option KernelMode
  | "full" => some .full
  | "list" => some .full -- backwards-compatible name for complete replay
  | "reconstruct" => some .reconstruct
  | _ => none

def kernelModeName : KernelMode → String
  | .full => "full"
  | .reconstruct => "reconstruct"

def rtpKind : ViprRtp → String
  | .infeas => "infeas"
  | .range _ _ => "range"

def isAsm : ViprReason → Bool
  | .asm => true
  | _ => false
def isLin : ViprReason → Bool
  | .lin _ => true
  | .linWeak _ _ => true
  | _ => false
def isRnd : ViprReason → Bool
  | .rnd _ => true
  | _ => false
def isUns : ViprReason → Bool
  | .uns _ _ _ _ => true
  | _ => false
def isSol : ViprReason → Bool
  | .sol => true
  | _ => false

def countReason (ders : Array ViprDer) (p : ViprReason → Bool) : Nat :=
  ders.foldl (fun n d => if p d.reason then n + 1 else n) 0

def reportCertificate (path : String) (v : Vipr) : IO Unit := do
  IO.println s!"file: {path}"
  IO.println s!"VER {v.version}  RTP {rtpKind v.rtp}"
  IO.println s!"vars {v.varNames.size}  int {v.intVars.length}  con {v.numCon}  steps {v.ders.size}"
  IO.println (s!"reasons: asm×{countReason v.ders isAsm}  "
    ++ s!"lin×{countReason v.ders isLin}  rnd×{countReason v.ders isRnd}  "
    ++ s!"uns×{countReason v.ders isUns}  sol×{countReason v.ders isSol}")

/-- Decode `bytes` as ISO-8859-1: each byte becomes the code point of the same
value.

Injective, so two names that differ as bytes still differ as strings. That
matters, because the checker compares variable names for duplicates. -/
def decodeLatin1 (bytes : ByteArray) : String :=
  bytes.foldl (fun s b => s.push (Char.ofNat b.toNat)) ""

/-- Read a certificate, tolerating names that are not UTF-8.

Published certificates in the `dfn6*` family carry ISO-8859-1 variable names
such as `München`, which `IO.FS.readFile` rejects with an uncaught exception.
The reference checker reads bytes and never looks inside a name, and neither
does this one, so the decoding only has to be deterministic and injective: try
UTF-8, and fall back to ISO-8859-1 for the whole file.

The fallback loses byte-level fidelity, because printing the certificate back
out re-encodes those names as UTF-8. `toString_roundtrip_of_parse` is unaffected:
it relates `parseVipr` and `toString` on the string that was parsed, whatever
produced it. -/
def readCertificate (path : String) : IO String := do
  let bytes ← IO.FS.readBinFile ⟨path⟩
  match String.fromUTF8? bytes with
  | some content => return content
  | none =>
      IO.eprintln s!"warning: {path} is not UTF-8; reading it as ISO-8859-1"
      return decodeLatin1 bytes

def parseFile (path : String) : IO (Except String (String × Vipr)) := do
  let content ← readCertificate path
  match parseVipr content with
  | .error e => return .error e
  | .ok v => return .ok (content, v)

def renderVipr (cert : Vipr) : String :=
  s!"({(repr cert).pretty 100000000} : Vipr)"

def emittedOptionRatDivision : String :=
  "private instance : HDiv (Option ℚ) Nat (Option ℚ) where\n"
  ++ "  hDiv q n := q.map (fun x => x / n)\n\n"

def viprReasonRefs : ViprReason → List Nat
  | .asm => []
  | .lin terms => terms.map Prod.fst
  | .linWeak bounds terms =>
      terms.map Prod.fst ++
        match bounds with
        | .global => []
        | .local localBounds => localBounds.map (·.rowIdx)
  | .rnd terms => terms.map Prod.fst
  | .uns i1 l1 i2 l2 => [i1, l1, i2, l2]
  | .sol => []

def mapWeakBounds (f : Nat → Nat) : ViprWeakBounds → ViprWeakBounds
  | .global => .global
  | .local bounds => .local (bounds.map fun bound => { bound with rowIdx := f bound.rowIdx })

def mapViprReason (f : Nat → Nat) : ViprReason → ViprReason
  | .asm => .asm
  | .lin terms => .lin (terms.map fun p => (f p.1, p.2))
  | .linWeak bounds terms =>
      .linWeak (mapWeakBounds f bounds) (terms.map fun p => (f p.1, p.2))
  | .rnd terms => .rnd (terms.map fun p => (f p.1, p.2))
  | .uns i1 l1 i2 l2 => .uns (f i1) (f l1) (f i2) (f l2)
  | .sol => .sol

def isLinWeak : ViprReason → Bool
  | .linWeak _ _ => true
  | _ => false

/-- Replace each incomplete `lin weak` reason with the ordinary linear combination
proposed by the completion algorithm. The ordinary checker still validates every
materialized combination, so this transformation is untrusted preprocessing. -/
def materializeWeakVipr (v : Vipr) : Vipr :=
  let table := boundTable v
  { v with
    ders := v.ders.mapIdx fun idx d =>
      match d.reason with
      | .linWeak bounds terms =>
          let comb := completeWeakComb v table idx (derStated v d) bounds terms
          { d with reason := .lin (comb.map fun p => (p.2, p.1)) }
      | _ => d }

/-- The test a closed row must pass for the claim: an absurdity for infeasibility, the
claimed objective bound for a range; `none` when the claim needs no derived row. Mirrors
the cases of `finalValid`. Untrusted: used only to root the slice and for the last-row
warning, never for the verdict. -/
def finalRowTest (v : Vipr) : Option (SLe → Bool) :=
  match v.rtp with
  | .infeas => some isAbsurd
  | .range lb ub =>
      if v.objSense = "min" then lb.map fun lower r => dominates r (objectiveLowerRow v lower)
      else if v.objSense = "max" then ub.map fun upper r => dominates r (objectiveUpperRow v upper)
      else none

/-- The last derivation whose stated row passes `finalRowTest`, which is the row the claim
rests on; the last derivation if none does. The VIPR specification puts that row last, but
exact SCIP sometimes writes further rows after it. -/
def provingDer (v : Vipr) : Nat := Id.run do
  let nder := v.ders.size
  let some test := finalRowTest v | return nder - 1
  for k in [:nder] do
    let i := nder - 1 - k
    if test (derStated v (v.ders.getD i default)) then
      return i
  return nder - 1

/-- Untrusted proof-producing slice. The generated reconstruction theorem separately
kernel-checks both the sliced replay and its row-subset relation to the original. -/
def sliceVipr (input : Vipr) : Vipr := Id.run do
  let v := materializeWeakVipr input
  if v.ders.isEmpty || v.cons.size != v.numCon then
    return v
  let ncon := v.numCon
  let nder := v.ders.size
  -- A range certificate retains every problem row so its checked solution witnesses
  -- and objective bounds describe exactly the original problem. Infeasibility can
  -- safely retain only the refuted row subset.
  let keepAllCon := match v.rtp with
    | .infeas => false
    | .range _ _ => true
  let mut keepCon := Array.replicate ncon keepAllCon
  let mut keepDer := Array.replicate nder false
  -- Root at the proving row, so rows written after it do not drop it from the slice.
  let mut todo : List Nat := [provingDer v]
  while !todo.isEmpty do
    let i := todo.headD 0
    todo := todo.tail
    if i < nder && !(keepDer.getD i false) then
      keepDer := keepDer.set! i true
      let d := v.ders.getD i default
      for ref in viprReasonRefs d.reason do
        if ref < ncon then
          keepCon := keepCon.setIfInBounds ref true
        else
          todo := (ref - ncon) :: todo
  let mut conRank := Array.replicate ncon 0
  let mut keptCon := 0
  for i in [:ncon] do
    conRank := conRank.set! i keptCon
    if keepCon.getD i false then keptCon := keptCon + 1
  let mut derRank := Array.replicate nder 0
  let mut keptDer := 0
  for i in [:nder] do
    derRank := derRank.set! i keptDer
    if keepDer.getD i false then keptDer := keptDer + 1
  let remap := fun ref =>
    if ref < ncon then conRank.getD ref 0
    else keptCon + derRank.getD (ref - ncon) 0
  let mut cons : Array ViprCon := #[]
  let mut numBounds := 0
  for i in [:ncon] do
    if keepCon.getD i false then
      let c := v.cons.getD i default
      cons := cons.push c
      if c.name.toList.head? == some 'B' then numBounds := numBounds + 1
  let mut ders : Array ViprDer := #[]
  for i in [:nder] do
    if keepDer.getD i false then
      let d := v.ders.getD i default
      ders := ders.push { d with reason := mapViprReason remap d.reason }
  return { v with numCon := keptCon, numBounds := numBounds, cons := cons, ders := ders }

def emitViprData (cert : Vipr) : String :=
  "import LeanVIPR.Spec.Semantics.Lower\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Parser\n\n"
  ++ emittedOptionRatDivision
  ++ s!"def cert : Vipr := {renderVipr cert}\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprReconstructionData (original sliced : Vipr) : String :=
  "import LeanVIPR.Spec.Semantics.Lower\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Parser\n\n"
  ++ emittedOptionRatDivision
  ++ s!"def original : Vipr := {renderVipr original}\n\n"
  ++ s!"def sliced : Vipr := {renderVipr sliced}\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprProof : String :=
  "import LeanVIPRGenerated.Data\n\n"
  ++ "import LeanVIPR.Thm.Checker.Sound\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Parser.Vipr LeanVIPR.Checker\n\n"
  ++ "theorem accepted : checkVipr cert = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified : LeanVIPR.Parser.Vipr.ClaimValid cert :=\n"
  ++ "  checkVipr_sound cert accepted\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end LeanVIPR.Generated\n"

def emitViprReconstructionProof : String :=
  "import LeanVIPRGenerated.Data\n\n"
  ++ "import LeanVIPR.Thm.Checker.Sound\n\n"
  ++ "set_option maxHeartbeats 0\n"
  ++ "set_option maxRecDepth 1000000\n\n"
  ++ "namespace LeanVIPR.Generated\n\n"
  ++ "open LeanVIPR.Parser.Vipr LeanVIPR.Semantics.Lower LeanVIPR.Checker\n\n"
  ++ "theorem slicedInfeas : sliced.rtp = .infeas := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem sameIntVars : sliced.intVars = original.intVars := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem rowsSubset : ∀ c ∈ conSLes sliced, c ∈ conSLes original := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem acceptedSlice : checkVipr sliced = true := by\n"
  ++ "  decide +kernel\n\n"
  ++ "theorem certified :\n"
  ++ "    ∀ a, Feasible original a → False :=\n"
  ++ "  checkViprInfeasibleSubset_sound original sliced slicedInfeas\n"
  ++ "    sameIntVars rowsSubset acceptedSlice\n\n"
  ++ "#print axioms certified\n\n"
  ++ "end LeanVIPR.Generated\n"

def generatedSourcePath (proofDir moduleName : String) : String :=
  s!"{proofDir}/LeanVIPRGenerated/{moduleName}.lean"

def generatedOleanPath (proofDir moduleName : String) : String :=
  s!"{proofDir}/LeanVIPRGenerated/{moduleName}.olean"

def runKernelModuleDirect (proofDir moduleName : String) : IO (Except String String) := do
  let sourcePath := generatedSourcePath proofDir moduleName
  let oleanPath := generatedOleanPath proofDir moduleName
  let inheritedLeanPath := (← IO.getEnv "LEAN_PATH").getD ""
  -- The proof directory comes last, so files planted there cannot shadow library
  -- modules; it only needs to supply the generated `LeanVIPRGenerated.*` modules.
  let localLeanPath :=
    if inheritedLeanPath.isEmpty then proofDir else inheritedLeanPath ++ ":" ++ proofDir
  let out ← IO.Process.output {
    cmd := "lean"
    args := #["-R", proofDir, "-o", oleanPath, sourcePath]
    env := #[("LEAN_PATH", some localLeanPath)] }
  if out.exitCode == 0 then
    return .ok (out.stdout ++ out.stderr)
  return .error (s!"kernel check failed in {moduleName} (exit {out.exitCode}):\n"
    ++ out.stdout ++ out.stderr)

def runKernelModulesDirect (proofDir : String) (moduleNames : List String) :
    IO (Except String String) := do
  let mut log := ""
  for moduleName in moduleNames do
    match ← runKernelModuleDirect proofDir moduleName with
    | .error e => return .error e
    | .ok out => log := log ++ out
  return .ok log

def runKernelModules (proofDir : String) (moduleNames : List String) :
    IO (Except String String) := do
  for moduleName in moduleNames do
    IO.println s!"kernel: {moduleName}"
  let lake := (← IO.getEnv "VIPR_LAKE").getD "lake"
  let self := (← IO.appPath).toString
  let out ← IO.Process.output {
    cmd := lake
    args := #["env", self, "--kernel-runner", proofDir] ++ moduleNames.toArray }
  if out.exitCode == 0 then
    return .ok (out.stdout ++ out.stderr)
  return .error s!"kernel runner exit {out.exitCode}:\n{out.stdout}{out.stderr}"

/-- How many tasks to split the replay into. One per core measured best; Lean exposes no
core count, so this reads `VIPRCHECK_TASKS` and otherwise takes a conservative default.
The value cannot affect the verdict -- `LeanVIPR.Thm.Checker.checkViprPar_eq` holds for
every task count -- so it is a tuning knob and nothing more. -/
def taskCount : IO Nat := do
  match ← IO.getEnv "VIPRCHECK_TASKS" with
  | some s => return (s.toNat?.getD 8).max 1
  | none => return 8

/-- The VIPR specification requires the *last* row to prove the claim; the checker accepts
any closed row (`HasClosedDominatingRow`). Say so when an accepted certificate relies on
that. Only when the last row cannot prove the claim at all is the pool rebuilt to name the
row that does, so conforming certificates cost nothing. A last row that passes the test but
still has open assumptions is not reported. -/
def warnIfNotLastRow (v : Vipr) : IO Unit := do
  let some test := finalRowTest v | return
  if (v.ders.back?.map (derStated v)).any test then return
  let pool := buildPool v (initialPool v) (viprSteps v)
  -- the last proving row: the one closest to where the specification expects it
  for k in [:pool.size] do
    let i := pool.size - 1 - k
    let e := pool.getD i default
    if decide (e.2 = ∅) && test e.1 then
      if i + 1 < pool.size then
        let name := if i < v.cons.size then (v.cons.getD i default).name
          else (v.ders.getD (i - v.cons.size) default).name
        let after := pool.size - 1 - i
        IO.eprintln (s!"warning: row {name} proves the claim but is not the last row, "
          ++ s!"which the VIPR specification requires ({after} "
          ++ (if after = 1 then "row follows" else "rows follow") ++ " it)")
      return

/-- Check with the compiled checker.

`useSlice` backward-slices an `RTP infeas` certificate and checks the slice. That
concludes the same thing about the original -- `checkViprSlice_sound` re-establishes every
side condition at run time -- for much less work, so it is the default. The slicer itself
is untrusted and could in principle emit a slice the checker rejects, so a failed slice
falls back to complete replay rather than rejecting; acceptance is therefore never lost
by slicing. Range certificates are always replayed completely. -/
def checkFileNative (path : String) (useSlice : Bool := true) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      reportCertificate path v
      let tasks ← taskCount
      let useSlice := useSlice && v.rtp == .infeas
      let accepted ← do
        if useSlice then
          let sliced := sliceVipr v
          IO.println (s!"slice: {v.cons.size} → {sliced.cons.size} constraints, "
            ++ s!"{v.ders.size} → {sliced.ders.size} steps")
          if checkViprSlicePar tasks v sliced then
            pure true
          else
            IO.println "slice check failed; falling back to complete replay"
            pure (checkViprPar tasks v)
        else
          pure (checkViprPar tasks v)
      if accepted then
        warnIfNotLastRow v
        IO.println "NATIVE ACCEPT  (verified array-backed checker; trusts the Lean compiler and runtime)"
        return 0
      else
        IO.eprintln "NATIVE REJECT  (checker returned false)"
        return 2

def reportInvalidReason (v : Vipr) (pool : CheckerPool)
    (original : ViprDer) (step : SStep) : IO Unit := do
  match step.reason with
  | .asm => IO.println "reason: asm"
  | .lin comb =>
      let resolved := resolveRefs pool comb
      let combined := scomb resolved
      IO.println s!"reason: lin ({comb.length} references)"
      IO.println s!"references-past: {referencesPast pool step.reason}"
      IO.println s!"linCheck: {linCheck step.stated resolved}"
      IO.println s!"formEq: {formEq combined.form step.stated.form}"
      IO.println s!"suitableLe: {suitableLe resolved}  suitableGe: {suitableGe resolved}"
      IO.println s!"combined rhs: {combined.rhs}  stated rhs: {step.stated.rhs}"
      IO.println s!"combined form: {repr (normForm combined.form)}"
      IO.println s!"stated form: {repr (normForm step.stated.form)}"
      match original.reason with
      | .linWeak _ terms =>
          IO.println s!"weak base references: {terms.length}"
          for correction in comb.drop terms.length do
            IO.println s!"weak correction: multiplier {correction.1}, row {correction.2}"
            let row := poolRow pool correction.2
            IO.println s!"correction row: {row.sense} {row.rhs} {repr (normForm row.form)}"
      | _ => pure ()
  | .rnd comb =>
      IO.println s!"reason: rnd ({comb.length} references)"
      IO.println s!"references-past: {referencesPast pool step.reason}"
      IO.println s!"rndCheck: {rndCheck v.intVars step.stated (resolveRefs pool comb)}"
  | .uns i1 l1 i2 l2 =>
      IO.println s!"reason: uns {i1} {l1} {i2} {l2}"
      IO.println s!"references-past: {referencesPast pool step.reason}"
      IO.println s!"branch 1 dominates: {dominates (poolRow pool i1) step.stated}"
      IO.println s!"branch 2 dominates: {dominates (poolRow pool i2) step.stated}"
      IO.println s!"complementary bounds: {
        unsBounds v.intVars (poolRow pool l1) (poolRow pool l2)}"
  | .sol => IO.println "reason: sol"

/-- Diagnostic command: report the first rejected derivation without changing acceptance. -/
def debugFirstInvalid (path : String) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      reportCertificate path v
      let steps := viprSteps v
      let mut pool := initialPool v
      let mut idx := 0
      for step in steps do
        let valid := stepValid v pool step
        if !valid then
          IO.eprintln s!"first invalid derivation: step {idx}, VIPR row {v.cons.size + idx}"
          let original := v.ders.getD idx default
          IO.eprintln s!"name: {original.name}"
          reportInvalidReason v pool original step
          return 2
        pool := pool.push (entryOf pool step)
        idx := idx + 1
      IO.println "all derivation steps pass"
      IO.println s!"final result: {solSection v && finalValid v pool}"
      return 0

/-- The axioms reported for the generated theorem must be among Lean's standard
axioms; in particular `sorryAx` or any user-declared axiom causes rejection. -/
def certifiedAxiomsOk (log : String) : Bool :=
  let flat := " ".intercalate (log.splitOn "\n")
  let key := "'LeanVIPR.Generated.certified' "
  match (flat.splitOn key).drop 1 with
  | [] => false
  | rest :: _ =>
      if rest.startsWith "does not depend on any axioms" then true
      else if rest.startsWith "depends on axioms: [" then
        let afterKey := ((rest.splitOn "depends on axioms: [").drop 1).headD ""
        let inner := (afterKey.splitOn "]").headD ""
        let names := (inner.splitOn ",").map (fun n => n.trimAscii.toString)
        names.all (· ∈ ["propext", "Classical.choice", "Quot.sound"])
      else false

/-- Diagnostic command: print every derivation's replayed reason after `lin weak`
completion, one line per derivation. Used to regression-test the untrusted completer. -/
def dumpMaterialized (path : String) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (_, v) =>
      for step in viprSteps v do
        match step.reason with
        | .lin comb => IO.println s!"lin {repr comb}"
        | .rnd comb => IO.println s!"rnd {repr comb}"
        | .uns i1 l1 i2 l2 => IO.println s!"uns {i1} {l1} {i2} {l2}"
        | .asm => IO.println "asm"
        | .sol => IO.println "sol"
      return 0

def checkFileKernel (path proofDir : String) (mode : KernelMode) : IO UInt32 := do
  match ← parseFile path with
  | .error e =>
      IO.eprintln s!"parse error: {e}"
      return 1
  | .ok (sourceText, v) =>
      reportCertificate path v
      let mut dataSource := ""
      let mut proofSource := ""
      let mut effectiveMode := mode
      match v.rtp with
      | .range _ _ =>
          match mode with
          | .full => pure ()
          | .reconstruct =>
              IO.println "range result: reconstruction is unavailable; using complete replay"
          effectiveMode := .full
          -- Emit the `lin weak`-completed certificate so the kernel does not rerun the
          -- completer; `ClaimValid.withDers` shows the claim is unchanged.
          let complete := materializeWeakVipr v
          if !checkViprPar (← taskCount) complete then
            IO.eprintln "REJECT  (native precheck found checkVipr = false)"
            return 2
          dataSource := emitViprData complete
          proofSource := emitViprProof
      | .infeas =>
          match mode with
          | .full =>
            let complete := materializeWeakVipr v
            if !checkViprPar (← taskCount) complete then
              IO.eprintln "REJECT  (native precheck found checkVipr = false)"
              return 2
            dataSource := emitViprData complete
            proofSource := emitViprProof
          | .reconstruct =>
              let sliced := sliceVipr v
              if checkViprPar (← taskCount) sliced then
                IO.println (s!"slice: {v.cons.size} → {sliced.cons.size} constraints, "
                  ++ s!"{v.ders.size} → {sliced.ders.size} steps")
                -- The reconstruction theorem reads only the original rows and integer
                -- declarations (`Feasible.withDers`), so the derivations are not emitted.
                dataSource := emitViprReconstructionData { v with ders := #[] } sliced
                proofSource := emitViprReconstructionProof
              else if checkViprPar (← taskCount) v then
                IO.println "slice precheck failed; falling back to complete replay"
                effectiveMode := .full
                dataSource := emitViprData (materializeWeakVipr v)
                proofSource := emitViprProof
              else
                IO.eprintln "REJECT  (native prechecks found no valid replay)"
                return 2
      let generatedDir := s!"{proofDir}/LeanVIPRGenerated"
      IO.FS.createDirAll ⟨generatedDir⟩
      IO.FS.writeFile ⟨generatedSourcePath proofDir "Data"⟩ dataSource
      IO.FS.writeFile ⟨generatedSourcePath proofDir "Proof"⟩ proofSource
      match ← runKernelModules proofDir ["Data", "Proof"] with
      | .error e =>
          IO.eprintln e
          return 2
      | .ok log =>
          if !log.isEmpty then IO.println log
          if !certifiedAxiomsOk log then
            IO.eprintln "REJECT  (generated theorem uses a nonstandard axiom or its axiom report is missing)"
            return 2
          warnIfNotLastRow v
          IO.println (s!"ACCEPT  (kernel-checked {kernelModeName effectiveMode}; "
            ++ "theorem LeanVIPR.Generated.certified)")
          IO.println s!"proof artifact: {generatedSourcePath proofDir "Proof"}"
          return 0

def runKernelMode (modeText path proofDir : String) : IO UInt32 := do
  match parseKernelMode? modeText with
  | none =>
      IO.eprintln s!"unknown kernel mode: {modeText}"
      return 1
  | some mode => checkFileKernel path proofDir mode

def main (args : List String) : IO UInt32 := do
  match args with
  | "--kernel-runner" :: proofDir :: moduleNames =>
      match ← runKernelModulesDirect proofDir moduleNames with
      | .error e =>
          IO.eprintln e
          return 2
      | .ok log =>
          if !log.isEmpty then IO.println log
          return 0
  | ["--native-mode", "slice", path] => checkFileNative path true
  | ["--native-mode", "full", path] => checkFileNative path false
  | ["--debug-first-invalid", path] => debugFirstInvalid path
  | ["--dump-materialized", path] => dumpMaterialized path
  | ["--kernel-mode", mode, path] =>
      runKernelMode mode path s!"/tmp/viprcheck_{mode}"
  | ["--kernel-mode", mode, path, "--proof-dir", proofDir] =>
      runKernelMode mode path proofDir
  | [path] => checkFileNative path true
  | _ =>
      IO.eprintln "Usage: viprcheck <certificate.vipr>"
      IO.eprintln "         Default. Compiled checker on a backward slice of the"
      IO.eprintln "         certificate, falling back to complete replay if the slice"
      IO.eprintln "         fails. Trusts the Lean compiler and runtime; prints"
      IO.eprintln "         NATIVE ACCEPT or NATIVE REJECT."
      IO.eprintln "       viprcheck --native-mode <slice|full> <certificate.vipr>"
      IO.eprintln "         slice: the default. full: replay every step. `full` proves"
      IO.eprintln "         nothing `slice` does not and is slower, so use it only to"
      IO.eprintln "         measure or to debug."
      IO.eprintln "       viprcheck --kernel-mode <full|reconstruct> <certificate.vipr>"
      IO.eprintln "                 [--proof-dir <dir>]"
      IO.eprintln "         Emit a Lean proof and have the kernel reduce the checker."
      IO.eprintln "         Minutes per certificate, and only small ones finish."
      IO.eprintln "       viprcheck --debug-first-invalid <certificate.vipr>"
      IO.eprintln "       viprcheck --dump-materialized <certificate.vipr>"
      IO.eprintln ""
      IO.eprintln "Environment:"
      IO.eprintln "  VIPRCHECK_TASKS=N  tasks for the parallel replay (default 8, N=1 for"
      IO.eprintln "                     sequential). Cannot change a verdict; see"
      IO.eprintln "                     LeanVIPR.Thm.Checker.checkViprPar_eq."
      IO.eprintln ""
      IO.eprintln "Exit codes: 0 accept, 1 usage or parse error, 2 reject."
      return 1
