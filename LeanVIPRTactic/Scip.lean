module

public import LeanVIPR

@[expose] public section

/-!
# Driving exact SCIP from `IO`

Stage 1 of `docs/TACTIC-TODO.md`: the untrusted transport. Given a `Mip`, write the MPS
file, run the solver with certificate output enabled, read the `.vipr` back and parse it.
Everything here is outside the trusted path — `Mip.pipeline_infeasible` mentions neither
the emitter, nor the solver, nor the parser, so a fault anywhere in this file can make the
tactic *fail* but cannot make it prove something false.

Deliberately plain `IO` and no metaprogramming, so it can be exercised with `#eval` before
any tactic exists. `LeanVIPRTactic/Command.lean` is the first caller.

## Which binary, and why it is checked by capability

Exact rational solving with VIPR output is in official SCIP 10, but a build without
`-DEXACTSOLVE=ON` (`docs/SCIP-SETUP.md`) cannot produce a certificate, and nothing it says
about itself reveals which kind it is:

* `--version` is indistinguishable — both report `[precision: 8 byte]` and neither
  mentions exact solving;
* the fraction probe the docs used to recommend (`x ≤ 1/2`, expecting `0.5` rather than
  the truncated `1`) tests whether `exact/enable` is *on*, not whether the build supports
  it. Measured here, 2026-11-10: *without* `set exact enable TRUE` both homebrew's
  `scip` 10.0.3 and our `-DEXACTSOLVE=ON` 10.0.1 truncate and answer `-1`; with it, both
  answer `-1/2`;
* the log says `storing certificate information in file <…>` before the solve, so it is
  not evidence that a certificate was produced.

So the probe asks for the thing the tactic actually needs, end to end: `x ≥ 1/2`,
`x ≤ 1/2` over the integers, which is infeasible *only* if `1/2` survives the round trip.
A certificate must appear, parse, `agreesWith` the Lean problem, be accepted by
`checkVipr`, and claim `RTP infeas`. The probe is the pipeline itself, on a problem small
enough to be free.

One operational note, learned the same way: SCIP resets the shell's working directory
during a run, so a relative `certificate filename` does not land where the caller expects.
Every path this file hands to SCIP is absolute.
-/

namespace LeanVIPR.Tactic

open LeanVIPR LeanVIPR.Parser LeanVIPR.Checker LeanVIPR.Impl.Encoder

/-! ## Configuration -/

/-- How to find and run the solver.

`binary := none` means: take `LEANVIPR_SCIP` if it is set, else `scip` from `PATH`.
`workDir := some d` keeps the `.mps` and `.vipr` in `d` instead of a temporary directory
that is deleted on the way out, which is what to reach for when a run needs inspecting. -/
structure ScipConfig where
  binary : Option String := none
  /-- Wall-clock limit in seconds, passed as `set limits time`. `none` is no limit. -/
  timeLimit : Option Nat := none
  /-- Run the capability probe before the real solve (once per binary per process). -/
  verifyBinary : Bool := true
  workDir : Option System.FilePath := none
  /-- The `NAME` field of the emitted problem. -/
  problemName : String := "leanvipr"
  deriving Inhabited

/-! ## Failure, as something a user can act on -/

/-- Why a run produced no certificate. Every constructor carries what the caller would
otherwise have to guess at, because the whole point of this layer is to fail legibly. -/
inductive ScipError where
  /-- No binary to run: nothing at `LEANVIPR_SCIP`, nothing named `scip` on `PATH`. -/
  | noBinary (tried : List String)
  /-- The binary ran, but is not a certifying build — the probe got no usable
  certificate. -/
  | notCertifying (binary : String) (detail : String)
  /-- The solver exited non-zero, or could not be spawned. -/
  | solverFailed (binary : String) (exitCode : UInt32) (log : String)
  /-- The solver succeeded and wrote no certificate file. -/
  | noCertificate (binary : String) (path : String) (log : String)
  /-- A certificate file was written that our parser rejects. -/
  | parseFailed (binary : String) (path : String) (msg : String)
  /-- The solver found the objective unbounded and wrote `RTP range -inf -infinity`, which
  the parser rightly rejects: VIPR v1.0 can state infeasibility or a range, not
  unboundedness. -/
  | unbounded (binary : String) (path : String)
  deriving Inhabited

/-- Trim a log to its last `n` lines, so an error message stays readable. -/
def lastLines (n : Nat) (log : String) : String :=
  let ls := log.splitOn "\n"
  String.intercalate "\n" (ls.drop (ls.length - min n ls.length))

def ScipError.message : ScipError → String
  | .noBinary tried =>
      "no SCIP binary found (tried: " ++ String.intercalate ", " tried ++ ").\n" ++
      "Build one with -DEXACTSOLVE=ON as in docs/SCIP-SETUP.md and point " ++
      "LEANVIPR_SCIP at it."
  | .notCertifying binary detail =>
      "the binary at " ++ binary ++ " did not pass the certificate probe: " ++ detail ++
      "\nSee docs/SCIP-SETUP.md for a build that does, and set LEANVIPR_SCIP to it."
  | .solverFailed binary code log =>
      "SCIP (" ++ binary ++ ") exited with code " ++ toString code ++ ":\n" ++
      lastLines 20 log
  | .noCertificate binary path log =>
      "SCIP (" ++ binary ++ ") reported success but wrote no certificate at " ++ path ++
      ".\n" ++ lastLines 20 log
  | .parseFailed binary path msg =>
      "the certificate SCIP (" ++ binary ++ ") wrote at " ++ path ++
      " does not parse: " ++ msg
  | .unbounded binary path =>
      "exact SCIP (" ++ binary ++ ") reports the objective unbounded: the certificate it " ++
      "wrote at " ++ path ++ " says `RTP range -inf -infinity`, and VIPR cannot certify " ++
      "unboundedness"

/-- Whether a certificate's text is SCIP's report of an unbounded objective: an `RTP` line
whose upper bound is `-infinity`. Only chooses an error message. -/
def reportsUnbounded (text : String) : Bool :=
  (text.splitOn "\n").any fun line =>
    match ((line.replace "\r" "").replace "\t" " ").splitOn " " |>.filter (· ≠ "") with
    | ["RTP", "range", _, "-infinity"] => true
    | _ => false

instance : ToString ScipError where
  toString e := e.message

/-! ## Locating the binary -/

/-- The binaries to try, in order: an explicit one, else `LEANVIPR_SCIP`, else `scip`. -/
def scipCandidates (cfg : ScipConfig) : IO (List String) := do
  match cfg.binary with
  | some b => return [b]
  | none =>
    match ← IO.getEnv "LEANVIPR_SCIP" with
    | some b => return [b, "scip"]
    | none => return ["scip"]

/-- Whether a binary can be spawned at all. `scip -v` is cheap and touches no files.

The exit code is part of the question: a missing executable does not raise here, it comes
back as a non-zero exit with `could not execute external process` on stderr, and reporting
that as a failed *probe* would send a reader looking for the wrong problem. -/
def canSpawn (binary : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := binary, args := #["-v"] }
    return out.exitCode == 0
  catch _ => return false

/-! ## One run -/

/-- The command line from `docs/SCIP-SETUP.md`: exact mode on, presolving and separation
off (neither is certified), certificate to `cert`, then read/optimize/quit. -/
def scipArgs (mps cert : System.FilePath) (timeLimit : Option Nat) : Array String :=
  let limit := match timeLimit with
    | none => #[]
    | some s => #["-c", "set limits time " ++ toString s]
  #["-c", "set exact enable TRUE",
    "-c", "set presolving maxrounds 0",
    "-c", "set separating maxrounds 0",
    "-c", "set separating maxroundsroot 0"] ++ limit ++
  #["-c", "set certificate filename " ++ cert.toString,
    "-c", "read " ++ mps.toString,
    "-c", "optimize",
    "-c", "quit"]

/-- What a successful run leaves us with: the certificate, and the three decisions the
pipeline theorems take as hypotheses. Keeping the `Bool`s next to the certificate means a
caller never has to remember which check belongs to which conclusion.

`mps` is retained for diagnostics only — nothing downstream reads it. -/
structure ScipRun where
  binary : String
  mps : String
  cert : Vipr
  /-- `agreesWith`: every certificate row is implied by a row of ours. Infeasibility. -/
  agrees : Bool
  /-- `relaxedByWith`: the converse direction. Needed to use a `SOL` entry. -/
  relaxedBy : Bool
  /-- `checkVipr`: the verified checker accepts the certificate. -/
  accepted : Bool
  /-- `objAgreesWith`: the certificate's objective is ours, once renamed. -/
  objAgrees : Bool
  /-- `objAgreesNegWith`: it is ours negated — the normal case for a maximization. -/
  objAgreesNeg : Bool
  deriving Inhabited

/-- Run the pipeline's checks against a parsed certificate. -/
def ScipRun.of (binary : String) (mps : String) (m : Mip) (v : Vipr) : ScipRun where
  binary := binary
  mps := mps
  cert := v
  agrees := agreesWith m v
  relaxedBy := relaxedByWith m v
  accepted := checkVipr v
  objAgrees := objAgreesWith m v
  objAgreesNeg := objAgreesNegWith m v

/-- What a certificate claims, for a report line. -/
def rtpSummary : ViprRtp → String
  | .infeas => "infeas"
  | .range lb ub =>
      let bound : Option ℚ → String
        | none => "-"
        | some q => toString q
      "range " ++ bound lb ++ " " ++ bound ub

/-- A one-paragraph report: what came back, and which pipeline theorem it feeds. -/
def ScipRun.summary (r : ScipRun) : String :=
  let yn (b : Bool) := if b then "yes" else "NO"
  "certificate: " ++ toString r.cert.varNames.size ++ " vars, " ++
    toString r.cert.cons.size ++ " cons, " ++ toString r.cert.ders.size ++ " ders, " ++
    "RTP " ++ rtpSummary r.cert.rtp ++ ", OBJ " ++ r.cert.objSense ++ "\n" ++
  "agreesWith: " ++ yn r.agrees ++ "   checkVipr: " ++ yn r.accepted ++
    "   relaxedByWith: " ++ yn r.relaxedBy ++ "\n" ++
  "objAgreesWith: " ++ yn r.objAgrees ++ "   objAgreesNegWith: " ++ yn r.objAgreesNeg

/-- Whether this run discharges `Mip.Infeasible` via `pipeline_infeasible`. -/
def ScipRun.provesInfeasible (r : ScipRun) : Bool :=
  r.agrees && r.accepted && r.cert.rtp == .infeas

/-- Encode `m`, solve it, parse the certificate back. No probe, no binary search: this is
the single run, factored out so the probe can use it too. -/
def runScipWith (cfg : ScipConfig) (binary : String) (m : Mip) :
    IO (Except ScipError ScipRun) := do
  let body (dir : System.FilePath) : IO (Except ScipError ScipRun) := do
    let mpsPath := dir / (cfg.problemName ++ ".mps")
    let certPath := dir / (cfg.problemName ++ ".vipr")
    let mps := encodeMpsNamed cfg.problemName m
    IO.FS.writeFile mpsPath mps
    let out ← try
        IO.Process.output { cmd := binary, args := scipArgs mpsPath certPath cfg.timeLimit }
      catch e =>
        return .error (.solverFailed binary 127 (toString e))
    let log := out.stdout ++ out.stderr
    if out.exitCode != 0 then
      return .error (.solverFailed binary out.exitCode log)
    if !(← certPath.pathExists) then
      return .error (.noCertificate binary certPath.toString log)
    let text ← IO.FS.readFile certPath
    match parseVipr text with
    | .error msg =>
        if reportsUnbounded text then return .error (.unbounded binary certPath.toString)
        return .error (.parseFailed binary certPath.toString msg)
    | .ok v => return .ok (ScipRun.of binary mps m v)
  match cfg.workDir with
  | some dir => do
      IO.FS.createDirAll dir
      -- Absolute, because SCIP resets its working directory mid-run.
      body (← IO.FS.realPath dir)
  | none => IO.FS.withTempDir body

/-! ## The capability probe

`x ≥ 1/2`, `x ≤ 1/2`, `x` integer in `[0,1]`. Infeasible — and infeasible *only* because
`1/2` is read exactly: a reader that truncates it to `1` sees `x = 1` and answers
`RTP range`. So one run tests the three things the tactic depends on at once: that a
certificate is written, that rationals survive the round trip, and that what comes back is
a certificate this checker accepts.

Measured alternative, rejected: `min -x s.t. x ≤ 1/2` continuous. Exact SCIP certifies its
bound with a `GlobalBound` row stated over `x` rather than over the objective, and
`checkVipr` does not accept that shape — a completeness gap, noted in
`docs/TACTIC-TODO.md`, and a bad thing to discover through a probe failure. An
infeasibility probe avoids the objective machinery entirely. -/

/-- The probe problem, as a `Mip`. -/
def probeMip : Mip where
  vars := #[{ name := "x", isInt := true, lo := some 0, hi := some 1 }]
  objSense := .min
  obj := [⟨0, 1⟩]
  rows := #[{ name := "c0", sense := 'G', rhs := 1/2, form := [⟨0, 1⟩] },
            { name := "c1", sense := 'L', rhs := 1/2, form := [⟨0, 1⟩] }]

/-- The claim the probe insists on seeing. A truncating reader answers `range` here. -/
def probeExpectedRtp : ViprRtp := .infeas

/-- Probe results, so a binary is probed once per process rather than once per goal. -/
initialize probeCache : IO.Ref (List (String × Bool)) ← IO.mkRef []

/-- Does this binary produce certificates the checker accepts, with rational fidelity? -/
def probeBinary (binary : String) : IO (Except ScipError Unit) := do
  if let some ok := (← probeCache.get).lookup binary then
    return if ok then .ok () else .error (.notCertifying binary "probe failed earlier")
  let record (ok : Bool) : IO Unit :=
    probeCache.modify (fun cs => (binary, ok) :: cs)
  let fail (detail : String) : IO (Except ScipError Unit) := do
    record false
    return .error (.notCertifying binary detail)
  match ← runScipWith { binary := some binary, verifyBinary := false,
                        problemName := "leanvipr_probe" } binary probeMip with
  | .error (.noCertificate ..) =>
      fail ("it wrote no certificate for a one-variable problem. The log is not " ++
        "evidence either way: SCIP announces `storing certificate information` before " ++
        "it knows whether it can produce one")
  | .error e => fail e.message
  | .ok r =>
    if r.cert.rtp != probeExpectedRtp then
      fail ("it answered `RTP " ++ rtpSummary r.cert.rtp ++ "` on `x ≥ 1/2 ∧ x ≤ 1/2`" ++
        " over the integers, rather than `RTP " ++ rtpSummary probeExpectedRtp ++
        "`, so it is not reading `1/2` exactly")
    else if !r.agrees then
      fail "the certificate it wrote does not agree with the problem we sent it"
    else if !r.accepted then
      fail "the certificate it wrote is rejected by checkVipr"
    else do
      record true
      return .ok ()

/-! ## The entry point -/

/-- Find a usable binary: the first candidate that spawns and (unless the check is
switched off) passes the probe.

On total failure the error reported is the *first* candidate's, not the last: candidates
are in preference order, so `LEANVIPR_SCIP` being the wrong build is the news, and
`scip` on `PATH` also being wrong is not. -/
def findScip (cfg : ScipConfig) : IO (Except ScipError String) := do
  let candidates ← scipCandidates cfg
  let mut firstError : Option ScipError := none
  for binary in candidates do
    if ← canSpawn binary then
      if !cfg.verifyBinary then
        return .ok binary
      match ← probeBinary binary with
      | .ok _ => return .ok binary
      | .error e => if firstError.isNone then firstError := some e
  return .error (firstError.getD (.noBinary candidates))

/-- **Stage 1.** Encode `m`, solve it with exact SCIP, parse the certificate, and run the
pipeline's checks against it. Fails with a `ScipError` rather than throwing, so a caller
in `MetaM` can turn it into a tactic error with no `try`/`catch`. -/
def runScip (m : Mip) (cfg : ScipConfig := {}) : IO (Except ScipError ScipRun) := do
  match ← findScip cfg with
  | .error e => return .error e
  | .ok binary => runScipWith cfg binary m

end LeanVIPR.Tactic
