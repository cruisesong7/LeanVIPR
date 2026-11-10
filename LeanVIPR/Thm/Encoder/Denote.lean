module

public import LeanVIPR.Thm.Encoder.Emit

@[expose] public section

/-!
# The emitted tokens denote the problem they came from

The second half of `mpsRoundTrip`. `Thm/Encoder/Emit.lean` proves the emitted text
tokenizes to `mpsToks n m`; this file is about showing those tokens derive `m` under
`Mps.IsMpsToks`.

**This file is incomplete.** What is proved is recorded here; what is not is listed at the
bottom with the shape each remaining obligation takes. Nothing is `sorry`ed — unfinished
obligations are simply absent, so a green build never overstates progress.

Worth restating why this half is optional. No pipeline theorem mentions `encodeMps`: a
faulty emitter makes SCIP solve a different problem, whose certificate `agreesWith` then
rejects. So this buys *completeness* — the pipeline never fails for reasons of our own
making — and never soundness.
-/

namespace LeanVIPR.Mps

open LeanVIPR LeanVIPR.Semantics LeanVIPR.Semantics.System LeanVIPR.Parser LeanVIPR.Impl

/-! ## Numbers the emitter writes are numbers the grammar reads -/

/-- `mpsRat` emits a token denoting its argument, whichever branch it takes. -/
theorem mpsRat_isNumTok (q : ℚ) : IsNumTok (Encoder.mpsRat q) q := by
  unfold Encoder.mpsRat
  split
  · rename_i hden
    obtain ⟨sign, ds, hprod, hval⟩ := printInt_isIntTok q.num
    refine Or.inl ⟨sign, ds, hprod, ?_⟩
    have : (q.num : ℚ) = q := by
      rw [(Rat.den_eq_one_iff q).mp (by simpa using hden)]
    rw [← this, hval]
  · exact printRat_isNumTok q

/-! ## The file splits along its section boundaries

Everything below needs this, and it is the one step that is purely mechanical: `map` and
`flatten` distribute over the appends in `mpsLines`. -/

theorem mpsToks_decompose (n : String) (m : Mip) :
    Encoder.mpsToks n m =
      ["NAME", n]
      ++ ((Encoder.objSenseLines m).map Prod.snd).flatten
      ++ ["ROWS"] ++ ((Encoder.rowsLines m).map Prod.snd).flatten
      ++ ["COLUMNS"] ++ ((Encoder.columnsLines m).map Prod.snd).flatten
      ++ ["RHS"] ++ ((Encoder.rhsLines m).map Prod.snd).flatten
      ++ ["BOUNDS"]
      ++ (((m.vars.toList.map Encoder.boundLines).flatten).map Prod.snd).flatten
      ++ ["ENDATA"] := by
  simp [Encoder.mpsToks, Encoder.mpsLines, List.map_append, List.flatten_append]

/-! ## The easy sections -/

theorem isNameSection (n : String) (hn : IsNameTok n) :
    IsNameSection ["NAME", n] := ⟨n, rfl, hn⟩

theorem isObjSenseSection (m : Mip) :
    IsObjSenseSection (((Encoder.objSenseLines m).map Prod.snd).flatten) m.objSense := by
  cases hm : m.objSense
  · exact Or.inl ⟨by simp [Encoder.objSenseLines, hm], rfl⟩
  · exact Or.inr ⟨"MAX", by simp [Encoder.objSenseLines, hm], Or.inr ⟨rfl, rfl⟩⟩

/-! ## The `IsSeq` sections

`ROWS` and `RHS` are a `map` over a list, so each is an induction whose step is one
entry. `IsSeq` is already the right combinator — `Thm/Parser/Printer.lean` uses it the
same way for the certificate's sections. -/

theorem isSeq_rowEntries (rs : List Mip.Row)
    (h : ∀ r ∈ rs, IsNameTok r.name ∧ (r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E')) :
    IsSeq IsRowEntry
      ((rs.map (fun r => ((Encoder.Indent.one, [r.sense.toString, r.name])
        : Encoder.Line))).map Prod.snd).flatten
      (rs.map (fun r => (r.sense, r.name))) := by
  induction rs with
  | nil => simpa using IsSeq.nil
  | cons r rs ih =>
      obtain ⟨hname, hsense⟩ := h r (by simp)
      have hrest := ih (fun s hs => h s (by simp [hs]))
      -- `IsSenseTok` lists the senses as `E ∨ L ∨ G`, `Mip.WellFormed` as `L ∨ G ∨ E`
      have hsense' : r.sense = 'E' ∨ r.sense = 'L' ∨ r.sense = 'G' := by
        rcases hsense with h | h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact Or.inl h
      have hhead : IsRowEntry [r.sense.toString, r.name] (r.sense, r.name) :=
        ⟨r.sense.toString, r.name, rfl, ⟨by simp, hsense'⟩, hname, rfl⟩
      simpa using IsSeq.cons hhead hrest

theorem isRowsSection (m : Mip)
    (hobj : IsNameTok Encoder.objRowName)
    (h : ∀ r ∈ m.rows, IsNameTok r.name ∧ (r.sense = 'L' ∨ r.sense = 'G' ∨ r.sense = 'E')) :
    IsRowsSection (((Encoder.rowsLines m).map Prod.snd).flatten) Encoder.objRowName
      (m.rows.toList.map (fun r => (r.sense, r.name))) := by
  refine ⟨_, ?_, hobj, isSeq_rowEntries m.rows.toList (fun r hr => h r (by simpa using hr))⟩
  simp [Encoder.rowsLines]

theorem isSeq_rhsEntries (rs : List Mip.Row)
    (hvec : IsNameTok "rhs") (h : ∀ r ∈ rs, IsNameTok r.name) :
    IsSeq IsRhsEntry
      ((rs.map (fun r => ((Encoder.Indent.four, ["rhs", r.name, Encoder.mpsRat r.rhs])
        : Encoder.Line))).map Prod.snd).flatten
      (rs.map (fun r => (r.name, r.rhs))) := by
  induction rs with
  | nil => simpa using IsSeq.nil
  | cons r rs ih =>
      have hrest := ih (fun s hs => h s (by simp [hs]))
      have hhead : IsRhsEntry ["rhs", r.name, Encoder.mpsRat r.rhs] (r.name, r.rhs) :=
        ⟨"rhs", r.name, Encoder.mpsRat r.rhs, rfl, hvec, h r (by simp),
          mpsRat_isNumTok r.rhs, rfl⟩
      simpa using IsSeq.cons hhead hrest

theorem isRhsSection (m : Mip) (hvec : IsNameTok "rhs")
    (h : ∀ r ∈ m.rows, IsNameTok r.name) :
    IsRhsSection (((Encoder.rhsLines m).map Prod.snd).flatten)
      (m.rows.toList.map (fun r => (r.name, r.rhs))) := by
  have := isSeq_rhsEntries m.rows.toList hvec (fun r hr => h r (by simpa using hr))
  simpa [IsRhsSection, Encoder.rhsLines] using this

/-! ## The `BOUNDS` section's syntax

The entries one variable contributes, then the concatenation over variables. Only the
*syntax* here — that the tokens derive some `BndEntry` list. Recovering `v.lo` and `v.hi`
from that list is a separate obligation, listed at the foot of this file. -/

/-- The `BndEntry` list one variable's lines derive. -/
def bndEntriesOf (v : Mip.Var) : List BndEntry :=
  (match v.lo with
   | none => [BndEntry.inf true v.name]
   | some l => [BndEntry.fin true v.name l]) ++
  (match v.hi with
   | none => if v.isInt then [BndEntry.inf false v.name] else []
   | some u => [BndEntry.fin false v.name u])

theorem isSeq_bndEntries (v : Mip.Var) (hvec : IsNameTok "BND") (hv : IsNameTok v.name) :
    IsSeq IsBndEntry (((Encoder.boundLines v).map Prod.snd).flatten) (bndEntriesOf v) := by
  have fin4 : ∀ (ty : String) (isLo : Bool) (q : ℚ),
      (ty = "LO" ∧ isLo = true) ∨ (ty = "UP" ∧ isLo = false) →
      IsBndEntry [ty, "BND", v.name, Encoder.mpsRat q] (BndEntry.fin isLo v.name q) := by
    intro ty isLo q h
    refine Or.inl ⟨ty, "BND", v.name, Encoder.mpsRat q, q, rfl, hvec, hv,
      mpsRat_isNumTok q, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  have inf3 : ∀ (ty : String) (isLo : Bool),
      (ty = "MI" ∧ isLo = true) ∨ (ty = "PL" ∧ isLo = false) →
      IsBndEntry [ty, "BND", v.name] (BndEntry.inf isLo v.name) := by
    intro ty isLo h
    refine Or.inr ⟨ty, "BND", v.name, rfl, hvec, hv, ?_⟩
    rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
  rcases hlo : v.lo with _ | lo <;> rcases hhi : v.hi with _ | hi <;>
    simp only [Encoder.boundLines, bndEntriesOf, hlo, hhi]
  · split
    · simpa using IsSeq.cons (inf3 "MI" true (Or.inl ⟨rfl, rfl⟩))
        (IsSeq.cons (inf3 "PL" false (Or.inr ⟨rfl, rfl⟩)) IsSeq.nil)
    · simpa using IsSeq.cons (inf3 "MI" true (Or.inl ⟨rfl, rfl⟩)) IsSeq.nil
  · simpa using IsSeq.cons (inf3 "MI" true (Or.inl ⟨rfl, rfl⟩))
      (IsSeq.cons (fin4 "UP" false hi (Or.inr ⟨rfl, rfl⟩)) IsSeq.nil)
  · split
    · simpa using IsSeq.cons (fin4 "LO" true lo (Or.inl ⟨rfl, rfl⟩))
        (IsSeq.cons (inf3 "PL" false (Or.inr ⟨rfl, rfl⟩)) IsSeq.nil)
    · simpa using IsSeq.cons (fin4 "LO" true lo (Or.inl ⟨rfl, rfl⟩)) IsSeq.nil
  · simpa using IsSeq.cons (fin4 "LO" true lo (Or.inl ⟨rfl, rfl⟩))
      (IsSeq.cons (fin4 "UP" false hi (Or.inr ⟨rfl, rfl⟩)) IsSeq.nil)

/-- `IsSeq` concatenates, which is what lets the per-variable bound entries compose. -/
theorem isSeq_append {α : Type} {R : Toks → α → Prop} :
    ∀ {a : Toks} {xs : List α}, IsSeq R a xs →
    ∀ {b : Toks} {ys : List α}, IsSeq R b ys → IsSeq R (a ++ b) (xs ++ ys) := by
  intro a xs ha
  induction ha with
  | nil => intro b ys hb; simpa using hb
  | cons h hs ih =>
      intro b ys hb
      simpa [List.append_assoc] using IsSeq.cons h (ih hb)

/-- The bound entries of a whole list of variables. Structural recursion rather than a
nested induction. -/
theorem isSeq_bndEntriesList (hvec : IsNameTok "BND") :
    ∀ (vs : List Mip.Var), (∀ v ∈ vs, IsNameTok v.name) →
    IsSeq IsBndEntry (((vs.map Encoder.boundLines).flatten).map Prod.snd).flatten
      ((vs.map bndEntriesOf).flatten)
  | [], _ => by simpa using IsSeq.nil
  | v :: vs, h => by
      have := isSeq_append (isSeq_bndEntries v hvec (h v (by simp)))
        (isSeq_bndEntriesList hvec vs (fun u hu => h u (by simp [hu])))
      simpa using this

theorem isBoundsSection (m : Mip) (hvec : IsNameTok "BND")
    (hv : ∀ v ∈ m.vars, IsNameTok v.name) :
    IsBoundsSection
      ((((m.vars.toList.map Encoder.boundLines).flatten).map Prod.snd).flatten)
      ((m.vars.toList.map bndEntriesOf).flatten) :=
  isSeq_bndEntriesList hvec m.vars.toList (fun v hv' => hv v (by simpa using hv'))

/-! ## Recovering a variable's bounds from the `BOUNDS` entries

Obligation 4. The folds scan every entry and keep the last match, so this needs the
variable-name `Nodup` from `Mip.WellFormed`: without it another variable's `LO` line could
shadow this one's. -/

/-- The step `loBound` folds with, named so facts about it are statable. -/
def loStep (x : String) (acc : Option ℚ) (e : BndEntry) : Option ℚ :=
  match e with
  | .fin true y q => if y = x then some q else acc
  | .inf true y => if y = x then none else acc
  | _ => acc

def hiStep (x : String) (acc : Option ℚ) (e : BndEntry) : Option ℚ :=
  match e with
  | .fin false y q => if y = x then some q else acc
  | .inf false y => if y = x then none else acc
  | _ => acc

/-- The variable an entry is about. -/
def bndName : BndEntry → String
  | .fin _ y _ => y
  | .inf _ y => y

theorem loBound_eq (es : List BndEntry) (x : String) :
    loBound es x = es.foldl (loStep x) none := rfl

theorem hiBound_eq (es : List BndEntry) (x : String) :
    hiBound es x = es.foldl (hiStep x) none := rfl

/-- Entries about other variables leave the fold alone. This is the lemma `Nodup` feeds. -/
theorem loStep_foldl_ne {x : String} : ∀ (es : List BndEntry),
    (∀ e ∈ es, bndName e ≠ x) → ∀ acc, es.foldl (loStep x) acc = acc
  | [], _, _ => rfl
  | e :: es, h, acc => by
      have hstep : loStep x acc e = acc := by
        cases e with
        | fin b y q => cases b <;> simp_all [loStep, bndName]
        | inf b y => cases b <;> simp_all [loStep, bndName]
      rw [List.foldl_cons, hstep]
      exact loStep_foldl_ne es (fun d hd => h d (by simp [hd])) acc

theorem hiStep_foldl_ne {x : String} : ∀ (es : List BndEntry),
    (∀ e ∈ es, bndName e ≠ x) → ∀ acc, es.foldl (hiStep x) acc = acc
  | [], _, _ => rfl
  | e :: es, h, acc => by
      have hstep : hiStep x acc e = acc := by
        cases e with
        | fin b y q => cases b <;> simp_all [hiStep, bndName]
        | inf b y => cases b <;> simp_all [hiStep, bndName]
      rw [List.foldl_cons, hstep]
      exact hiStep_foldl_ne es (fun d hd => h d (by simp [hd])) acc

/-- A variable's own block sets its lower bound outright, whatever the accumulator was. -/
theorem loStep_foldl_own (v : Mip.Var) (acc : Option ℚ) :
    (bndEntriesOf v).foldl (loStep v.name) acc = v.lo := by
  rcases hlo : v.lo with _ | lo <;> rcases hhi : v.hi with _ | hi <;>
    simp [bndEntriesOf, hlo, hhi, loStep] <;> split <;> simp [loStep]

/-- The upper bound needs the initial `none`, unlike the lower: a continuous variable with
no upper bound emits no upper entry at all, so the fold has nothing to set and relies on
where it started. The caller always has `none` there, because by `Nodup` every earlier
entry is about a different variable. -/
theorem hiStep_foldl_own (v : Mip.Var) :
    (bndEntriesOf v).foldl (hiStep v.name) none = v.hi := by
  rcases hlo : v.lo with _ | lo <;> rcases hhi : v.hi with _ | hi <;>
    simp [bndEntriesOf, hlo, hhi, hiStep] <;> split <;> simp [hiStep]

/-- `bndEntriesOf v` only ever talks about `v`. -/
theorem bndName_mem (v : Mip.Var) : ∀ e ∈ bndEntriesOf v, bndName e = v.name := by
  intro e he
  rcases hlo : v.lo with _ | lo <;> rcases hhi : v.hi with _ | hi <;>
    simp only [bndEntriesOf, hlo, hhi] at he <;> simp_all
  all_goals (rcases he with rfl | ⟨-, rfl⟩ <;> rfl)

/-- **Obligation 4, lower half.** -/
theorem loBound_flatten : ∀ (vs : List Mip.Var), (vs.map Mip.Var.name).Nodup →
    ∀ v ∈ vs, loBound ((vs.map bndEntriesOf).flatten) v.name = v.lo
  | [], _, _, h => by simp at h
  | w :: vs, hnd, v, hv => by
      have hnd' : (vs.map Mip.Var.name).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
      have hwnot : w.name ∉ vs.map Mip.Var.name :=
        (List.nodup_cons.mp (by simpa using hnd)).1
      rw [loBound_eq]
      simp only [List.map_cons, List.flatten_cons, List.foldl_append]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [loStep_foldl_own v none]
        refine loStep_foldl_ne _ ?_ _
        intro e he
        obtain ⟨es, hes, he⟩ := List.mem_flatten.mp he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hes
        rw [bndName_mem u e he]
        exact fun hcontra => hwnot (by rw [← hcontra]; exact List.mem_map_of_mem hu)
      · have hne : w.name ≠ v.name := fun hcontra =>
          hwnot (hcontra ▸ List.mem_map_of_mem hv)
        rw [loStep_foldl_ne (bndEntriesOf w) (fun e he => by
          rw [bndName_mem w e he]; exact hne) none]
        have := loBound_flatten vs hnd' v hv
        rwa [loBound_eq] at this

/-- **Obligation 4, upper half.** -/
theorem hiBound_flatten : ∀ (vs : List Mip.Var), (vs.map Mip.Var.name).Nodup →
    ∀ v ∈ vs, hiBound ((vs.map bndEntriesOf).flatten) v.name = v.hi
  | [], _, _, h => by simp at h
  | w :: vs, hnd, v, hv => by
      have hnd' : (vs.map Mip.Var.name).Nodup := (List.nodup_cons.mp (by simpa using hnd)).2
      have hwnot : w.name ∉ vs.map Mip.Var.name :=
        (List.nodup_cons.mp (by simpa using hnd)).1
      rw [hiBound_eq]
      simp only [List.map_cons, List.flatten_cons, List.foldl_append]
      rcases List.mem_cons.mp hv with rfl | hv
      · rw [hiStep_foldl_own v]
        refine hiStep_foldl_ne _ ?_ _
        intro e he
        obtain ⟨es, hes, he⟩ := List.mem_flatten.mp he
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hes
        rw [bndName_mem u e he]
        exact fun hcontra => hwnot (by rw [← hcontra]; exact List.mem_map_of_mem hu)
      · have hne : w.name ≠ v.name := fun hcontra =>
          hwnot (hcontra ▸ List.mem_map_of_mem hv)
        rw [hiStep_foldl_ne (bndEntriesOf w) (fun e he => by
          rw [bndName_mem w e he]; exact hne) none]
        have := hiBound_flatten vs hnd' v hv
        rwa [hiBound_eq] at this

/-! ## The `COLUMNS` section's syntax

Obligation 1. Two things make this the awkward section: it emits marker lines *between*
columns, so the recursion has to carry the marker state, and the marker's own name must be
a token the grammar reads back. -/

theorem keywords_noDigit : ∀ k ∈ sectionKeywords, ∀ c ∈ k.toList, ¬ c.isDigit := by decide
theorem markerTok_noDigit : ∀ c ∈ markerTok.toList, ¬ c.isDigit := by decide

/-- A marker's name is readable back as a name. The argument is uniform rather than
case-by-case over the keywords: every structurally-read token is digit-free, while
`printNat` emits digits, so they cannot coincide. -/
theorem isNameTok_markerName (n : Nat) : IsNameTok ("M" ++ printNat n) := by
  obtain ⟨hdne, hdig⟩ := (printNat_isNatTok n).1
  obtain ⟨d, hd⟩ : ∃ d, d ∈ (printNat n).toList := by
    cases hl : (printNat n).toList with
    | nil => exact absurd hl hdne
    | cons c cs => exact ⟨c, by simp⟩
  have hdd : d.isDigit := hdig d hd
  have hmem : d ∈ ("M" ++ printNat n).toList := by simp [hd]
  refine ⟨by simp, (printableTok_markerName n).2.1, by simp, ?_, ?_⟩
  · exact fun hk => keywords_noDigit _ hk d hmem hdd
  · intro hk
    exact markerTok_noDigit d (by rw [← hk]; exact hmem) hdd

/-- The `ColEntry` list `columnsAux` emits, mirroring its structure. -/
def colEntriesOf (m : Mip) : List (Nat × Mip.Var) → Bool → Nat → List ColEntry
  | [], inInt, mk => if inInt then [.marker ("M" ++ printNat mk) false] else []
  | (j, v) :: rest, inInt, mk =>
      let opening := v.isInt && !inInt
      let closing := !v.isInt && inInt
      let pre :=
        if opening then [ColEntry.marker ("M" ++ printNat mk) true]
        else if closing then [ColEntry.marker ("M" ++ printNat mk) false]
        else []
      let mk' := if opening || closing then mk + 1 else mk
      let es := Encoder.colEntries m j
      let es := if es.isEmpty then [(Encoder.objRowName, (0 : ℚ))] else es
      pre ++ es.map (fun e => ColEntry.coeff v.name e.1 e.2)
          ++ colEntriesOf m rest v.isInt mk'

/-- One marker line derives one marker entry. -/
theorem isColEntry_marker (mk : Nat) (tag : String) (b : Bool)
    (h : (tag = "INTORG" ∧ b = true) ∨ (tag = "INTEND" ∧ b = false)) :
    IsColEntry (Encoder.markerLine mk tag).2
      (ColEntry.marker ("M" ++ printNat mk) b) := by
  refine Or.inl ⟨"M" ++ printNat mk, "'" ++ tag ++ "'", rfl,
    isNameTok_markerName mk, ?_⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- One column's coefficient lines derive its coefficient entries. -/
theorem isSeq_colLines {name : String} (hn : IsNameTok name) :
    ∀ (es : List (String × ℚ)), (∀ e ∈ es, IsNameTok e.1) →
    IsSeq IsColEntry (((Encoder.colLines name es).map Prod.snd).flatten)
      (es.map (fun e => ColEntry.coeff name e.1 e.2))
  | [], _ => by simpa [Encoder.colLines] using IsSeq.nil
  | e :: es, h => by
      have hhead : IsColEntry [name, e.1, Encoder.mpsRat e.2]
          (ColEntry.coeff name e.1 e.2) :=
        Or.inr ⟨name, e.1, Encoder.mpsRat e.2, e.2, rfl, hn, h e (by simp),
          mpsRat_isNumTok e.2, rfl⟩
      have := IsSeq.cons hhead (isSeq_colLines hn es (fun d hd => h d (by simp [hd])))
      simpa [Encoder.colLines] using this

/-- A column's entries are keyed by a row name or by the objective row. The `IsNameTok`
analogue of `printableTok_colEntry`: the grammar needs the stronger property, since a row
called `COLUMNS` would break the section split rather than merely fail to print. -/
theorem isNameTok_colEntry (m : Mip) (hobj : IsNameTok Encoder.objRowName)
    (hrow : ∀ r ∈ m.rows, IsNameTok r.name) (j : Nat) :
    ∀ e ∈ Encoder.colEntries m j, IsNameTok e.1 := by
  intro e he
  simp only [Encoder.colEntries, List.mem_append] at he
  rcases he with he | he
  · split at he
    · simp at he
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      subst he; exact hobj
  · obtain ⟨r, hr, he⟩ := List.mem_filterMap.mp he
    split at he
    · simp at he
    · simp only [Option.some.injEq] at he
      subst he
      exact hrow r (by simpa using hr)

/-- **Obligation 1.** The whole `COLUMNS` section, by recursion carrying the marker state.
The two `split`s mirror the emitter's own `if opening … else if closing …`, so the
structure of the proof follows the structure of `columnsAux` exactly. -/
theorem isSeq_columnsAux (m : Mip) (hobj : IsNameTok Encoder.objRowName)
    (hrow : ∀ r ∈ m.rows, IsNameTok r.name) :
    ∀ (vs : List (Nat × Mip.Var)) (inInt : Bool) (mk : Nat),
      (∀ p ∈ vs, IsNameTok p.2.name) →
      IsSeq IsColEntry
        (((Encoder.columnsAux m vs inInt mk).map Prod.snd).flatten)
        (colEntriesOf m vs inInt mk)
  | [], inInt, mk, _ => by
      simp only [Encoder.columnsAux, colEntriesOf]
      split
      · simpa using IsSeq.cons
          (isColEntry_marker mk "INTEND" false (Or.inr ⟨rfl, rfl⟩)) IsSeq.nil
      · simpa using IsSeq.nil
  | (j, v) :: rest, inInt, mk, hvs => by
      have hentries : ∀ e ∈ (if (Encoder.colEntries m j).isEmpty then
            [(Encoder.objRowName, (0 : ℚ))] else Encoder.colEntries m j), IsNameTok e.1 := by
        split
        · intro e he
          simp only [List.mem_cons, List.not_mem_nil, or_false] at he
          subst he; exact hobj
        · exact isNameTok_colEntry m hobj hrow j
      have hcols := isSeq_colLines (hvs (j, v) (by simp)) _ hentries
      have hrec := isSeq_columnsAux m hobj hrow rest v.isInt
        (if (v.isInt && !inInt) || (!v.isInt && inInt) then mk + 1 else mk)
        (fun p hp => hvs p (by simp [hp]))
      simp only [Encoder.columnsAux, colEntriesOf]
      split
      · simpa [List.append_assoc] using IsSeq.cons
          (isColEntry_marker mk "INTORG" true (Or.inl ⟨rfl, rfl⟩))
          (isSeq_append hcols hrec)
      · split
        · simpa [List.append_assoc] using IsSeq.cons
            (isColEntry_marker mk "INTEND" false (Or.inr ⟨rfl, rfl⟩))
            (isSeq_append hcols hrec)
        · simpa using isSeq_append hcols hrec

theorem isColumnsSection (m : Mip) (hobj : IsNameTok Encoder.objRowName)
    (hrow : ∀ r ∈ m.rows, IsNameTok r.name) (hv : ∀ v ∈ m.vars, IsNameTok v.name) :
    IsColumnsSection (((Encoder.columnsLines m).map Prod.snd).flatten)
      (colEntriesOf m (m.vars.toList.mapIdx (fun j v => (j, v))) false 1) :=
  isSeq_columnsAux m hobj hrow _ _ _ (by
    intro p hp
    obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hp
    have hp2 : p.2 = m.vars.toList[i] := by rw [← he]
    rw [hp2]
    exact hv _ (by simpa using List.getElem_mem hi))

/-! ## The marker interleaving

Obligation 2, and the one that is about the *arrangement* of entries rather than about any
single entry: the `INTORG`/`INTEND` pairs must bracket exactly the integer columns. The
proof threads a marker state, so `intColumns` and `stateAfter` are given decomposition
lemmas first and the invariant is then one line per case. -/

/-- The marker state an entry list leaves behind. -/
def stateAfter : List ColEntry → Bool → Bool
  | [], b => b
  | .marker _ b :: rest, _ => stateAfter rest b
  | .coeff _ _ _ :: rest, b => stateAfter rest b

/-- `intColumns` splits along an append, threading the marker state. -/
theorem intColumns_append : ∀ (es1 es2 : List ColEntry) (b : Bool),
    intColumns (es1 ++ es2) b = intColumns es1 b ++ intColumns es2 (stateAfter es1 b)
  | [], es2, b => by simp [intColumns, stateAfter]
  | .marker n c :: rest, es2, b => by
      simpa [intColumns, stateAfter] using intColumns_append rest es2 c
  | .coeff c r q :: rest, es2, b => by
      have := intColumns_append rest es2 b
      cases b <;> simp [intColumns, stateAfter, this]

/-- `stateAfter` threads through an append. -/
theorem stateAfter_append : ∀ (es1 es2 : List ColEntry) (b : Bool),
    stateAfter (es1 ++ es2) b = stateAfter es2 (stateAfter es1 b)
  | [], _, _ => rfl
  | .marker n c :: rest, es2, b => by
      simpa [stateAfter] using stateAfter_append rest es2 c
  | .coeff c r q :: rest, es2, b => by
      simpa [stateAfter] using stateAfter_append rest es2 b

/-- Markers only: no columns declared, and the state is whatever the last marker said. -/
theorem intColumns_markers_nil (n : String) (c b : Bool) :
    intColumns [ColEntry.marker n c] b = [] := by simp [intColumns]

theorem stateAfter_marker (n : String) (c b : Bool) :
    stateAfter [ColEntry.marker n c] b = c := by simp [stateAfter]

theorem stateAfter_nil (b : Bool) : stateAfter [] b = b := rfl

/-- Coefficient entries never change the state. -/
theorem stateAfter_coeffs : ∀ (es : List (String × ℚ)) (name : String) (b : Bool),
    stateAfter (es.map (fun e => ColEntry.coeff name e.1 e.2)) b = b
  | [], _, _ => rfl
  | e :: es, name, b => by simpa [stateAfter] using stateAfter_coeffs es name b

/-- In state `true` every coefficient entry declares its column; in state `false`, none. -/
theorem intColumns_coeffs : ∀ (es : List (String × ℚ)) (name : String) (b : Bool),
    intColumns (es.map (fun e => ColEntry.coeff name e.1 e.2)) b =
      if b then es.map (fun _ => name) else []
  | [], _, b => by cases b <;> simp [intColumns]
  | e :: es, name, b => by
      have := intColumns_coeffs es name b
      cases b <;> simp [intColumns, this]

/-- **The invariant.** Whatever state a column is reached in, the markers the emitter puts
before it leave the state equal to that column's own integrality. This is what makes the
`INTORG`/`INTEND` pairs bracket exactly the integer columns. -/
theorem stateAfter_pre (v : Mip.Var) (inInt : Bool) (mk : Nat) :
    stateAfter
      (if v.isInt && !inInt then [ColEntry.marker ("M" ++ printNat mk) true]
       else if !v.isInt && inInt then [ColEntry.marker ("M" ++ printNat mk) false]
       else []) inInt = v.isInt := by
  cases hv : v.isInt <;> cases inInt <;> simp [stateAfter]

/-- The entry list the emitter gives a column is never empty, so an integer column always
contributes its name. -/
theorem colBlock_ne_nil (m : Mip) (j : Nat) :
    (if (Encoder.colEntries m j).isEmpty then [(Encoder.objRowName, (0 : ℚ))]
     else Encoder.colEntries m j) ≠ [] := by
  split
  · simp
  · rename_i h; simpa [List.isEmpty_iff] using h

theorem mem_intColumns_colEntriesOf (m : Mip) (x : String) :
    ∀ (vs : List (Nat × Mip.Var)) (inInt : Bool) (mk : Nat),
      (x ∈ intColumns (colEntriesOf m vs inInt mk) inInt ↔
        ∃ p ∈ vs, p.2.isInt = true ∧ p.2.name = x)
  | [], inInt, mk => by
      simp only [colEntriesOf]
      split <;> simp [intColumns]
  | (j, v) :: rest, inInt, mk => by
      have hrec := mem_intColumns_colEntriesOf m x rest v.isInt
        (if (v.isInt && !inInt) || (!v.isInt && inInt) then mk + 1 else mk)
      simp only [colEntriesOf, intColumns_append, stateAfter_append,
        stateAfter_pre v inInt mk, stateAfter_coeffs, intColumns_coeffs]
      have hpre : intColumns
          (if v.isInt && !inInt then [ColEntry.marker ("M" ++ printNat mk) true]
           else if !v.isInt && inInt then [ColEntry.marker ("M" ++ printNat mk) false]
           else []) inInt = [] := by
        cases hv : v.isInt <;> cases inInt <;> simp [hv, intColumns]
      rw [hpre]
      cases hv : v.isInt <;> simp only [hv] at hrec
      · simpa [hv] using hrec
      · simp only [ite_true, List.nil_append, List.mem_append, List.mem_map]
        constructor
        · rintro (⟨e, _, rfl⟩ | h)
          · exact ⟨(j, v), by simp, hv, rfl⟩
          · obtain ⟨p, hp, hpi, hpx⟩ := hrec.mp h
            exact ⟨p, by simp [hp], hpi, hpx⟩
        · rintro ⟨p, hp, hpi, hpx⟩
          rcases List.mem_cons.mp hp with rfl | hp
          · obtain ⟨e, he⟩ : ∃ e, e ∈ (if (Encoder.colEntries m j).isEmpty then
                [(Encoder.objRowName, (0 : ℚ))] else Encoder.colEntries m j) := by
              cases hl : (if (Encoder.colEntries m j).isEmpty then
                  [(Encoder.objRowName, (0 : ℚ))] else Encoder.colEntries m j) with
              | nil => exact absurd hl (colBlock_ne_nil m j)
              | cons a as => exact ⟨a, by simp⟩
            exact Or.inl ⟨e, he, hpx⟩
          · exact Or.inr (hrec.mpr ⟨p, hp, hpi, hpx⟩)


/-- **Obligation 2.** A column is declared integral exactly when its variable is.

`Nodup` is what rules out a *different* variable with the same name having been the one
declared; without it the left-to-right direction fails. -/
theorem declaresInt_iff (m : Mip) (hnd : (m.vars.toList.map Mip.Var.name).Nodup)
    (v : Mip.Var) (hv : v ∈ m.vars) :
    DeclaresInt (colEntriesOf m (m.vars.toList.mapIdx (fun j w => (j, w))) false 1)
        v.name ↔ v.isInt = true := by
  rw [DeclaresInt, mem_intColumns_colEntriesOf]
  constructor
  · rintro ⟨p, hp, hpi, hpx⟩
    obtain ⟨i, hi, he⟩ := List.mem_mapIdx.mp hp
    have hp2 : p.2 = m.vars.toList[i] := by rw [← he]
    have hmem : p.2 ∈ m.vars.toList := by rw [hp2]; exact List.getElem_mem hi
    have : p.2 = v := by
      have hvl : v ∈ m.vars.toList := by simpa using hv
      exact List.inj_on_of_nodup_map hnd hmem hvl hpx
    rwa [this] at hpi
  · intro hvi
    obtain ⟨i, hi, hiv⟩ : ∃ i, ∃ h : i < m.vars.toList.length, m.vars.toList[i] = v := by
      obtain ⟨i, hi⟩ := List.mem_iff_getElem.mp (by simpa using hv : v ∈ m.vars.toList)
      exact ⟨i, hi⟩
    exact ⟨(i, v), List.mem_mapIdx.mpr ⟨i, hi, by rw [hiv]⟩, hvi, rfl⟩

/-! ## The grouped sum

The ingredient obligation 3 was missing. `Thm.System.LinForm.normForm_eval` is the
analogous statement over `Valuation`; what the transpose needs is the `RealValuation` one,
and it is proved here by induction rather than through `Finset`, which is not in this
development's import surface. -/

/-- A sum over `range k` whose term vanishes off one index. Proved by induction rather than
through `Finset`, which is not in this development's import surface. -/
theorem sum_range_single (a : Nat → ℝ) (c : ℝ) : ∀ (k i : Nat),
    ((List.range k).map (fun j => (if i = j then c else 0) * a j)).sum
      = if i < k then c * a i else 0
  | 0, i => by simp
  | k + 1, i => by
      rw [List.range_succ]
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, sum_range_single a c k i]
      rcases lt_trichotomy i k with h | h | h
      · rw [if_pos h, if_pos (by omega : i < k + 1), if_neg (by omega : ¬ i = k)]
        simp
      · subst h
        rw [if_neg (by omega : ¬ i < i), if_pos (by omega : i < i + 1)]
        simp
      · rw [if_neg (by omega : ¬ i < k), if_neg (by omega : ¬ i = k),
          if_neg (by omega : ¬ i < k + 1)]
        simp

theorem sum_map_add {α : Type} (l : List α) (A B : α → ℝ) :
    (l.map (fun x => A x + B x)).sum = (l.map A).sum + (l.map B).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih]; ring

/-- `coeffOf` as a plain sum rather than a fold, which is what makes it additive in the
form. -/
def coeffAt (f : LinForm) (j : Nat) : ℚ :=
  (f.map (fun t => if t.idx = j then t.coeff else 0)).sum

theorem coeffOf_eq_coeffAt : ∀ (f : LinForm) (j : Nat) (acc : ℚ),
    f.foldl (fun a t => if t.idx == j then a + t.coeff else a) acc = acc + coeffAt f j
  | [], j, acc => by simp [coeffAt]
  | t :: f, j, acc => by
      rw [List.foldl_cons]
      by_cases h : t.idx = j
      · rw [show (if t.idx == j then acc + t.coeff else acc) = acc + t.coeff by simp [h],
          coeffOf_eq_coeffAt f j (acc + t.coeff)]
        simp [coeffAt, h]
        ring
      · rw [show (if t.idx == j then acc + t.coeff else acc) = acc by simp [h],
          coeffOf_eq_coeffAt f j acc]
        simp [coeffAt, h]

theorem coeffOf_eq (f : LinForm) (j : Nat) : Encoder.coeffOf f j = coeffAt f j := by
  unfold Encoder.coeffOf
  simpa using coeffOf_eq_coeffAt f j 0

/-- **The grouped sum**, the ingredient the transpose was missing. Reconstructing a form
by index and evaluating gives the same real number as evaluating the original, provided
every index it mentions is in range. `Thm.System.LinForm.normForm_eval` is the analogous
statement over `Valuation`; this is the `RealValuation` one. -/
theorem sum_range_coeffAt (a : RealValuation) (k : Nat) : ∀ (f : LinForm),
    (∀ t ∈ f, t.idx < k) →
    ((List.range k).map (fun j => ((coeffAt f j : ℚ) : ℝ) * a j)).sum = evalReal f a
  | [], _ => by simp [coeffAt, evalReal]
  | t :: f, h => by
      have ht : t.idx < k := h t (by simp)
      have hrest := sum_range_coeffAt a k f (fun s hs => h s (by simp [hs]))
      have hsplit : (fun j => ((coeffAt (t :: f) j : ℚ) : ℝ) * a j)
          = (fun j => (if t.idx = j then (t.coeff : ℝ) else 0) * a j
              + ((coeffAt f j : ℚ) : ℝ) * a j) := by
        funext j
        by_cases hj : t.idx = j
        · simp [coeffAt, hj]; push_cast; ring
        · simp [coeffAt, hj]
      rw [hsplit, sum_map_add, sum_range_single a (t.coeff : ℝ) k t.idx, hrest]
      simp [ht, evalReal]


/-! ## What is still open

Eight of the nine obligations in `IsMpsToks` are discharged above, and the one
remaining has had its missing ingredient supplied: the decomposition, and
the `NAME`, `OBJSENSE`, `ROWS`, `RHS` and `BOUNDS` *syntax*. One remains, and it is the
semantic one — each relates a section's recovered contents back to `m`, rather than
saying which tokens derive which entries.

~~**1. `COLUMNS` syntax.**~~ **Done** — `isColumnsSection`, by a recursion carrying the
marker state whose `split`s mirror the emitter's own `if opening … else if closing …`. The
enabler was `isNameTok_markerName`: a marker's name must be readable back, and the
argument for it is uniform rather than case-by-case over the keywords — every
structurally-read token is digit-free, `printNat` emits digits, so they cannot coincide.

~~**2. `DeclaresInt cols v.name ↔ v.isInt`.**~~ **Done** — `declaresInt_iff`. The property
is about the *arrangement* of entries rather than any one entry, so the proof threads a
marker state: `stateAfter` plus decomposition lemmas for it and `intColumns` over an
append, after which the invariant (`stateAfter_pre`) is one line per case. `Nodup` is what
rules out a different variable with the same name having been the one declared.

**3. `FormEqReal (rowForm cols names r.name) r.form`.** The transpose. The ingredient this
was blocked on is now **proved** — `sum_range_coeffAt`, the grouped sum over `ℝ`, together
with `coeffOf_eq` relating the emitter's fold to a plain sum. Three steps remain, all
bookkeeping rather than mathematics:

* `evalReal (rowForm es names row) a = ∑_{j < names.length} colCoeff es names[j] row * a j`.
  Two wrinkles: `rowForm`'s `if q = 0 then [] else _` skip (harmless, since a skipped
  index would have contributed `0 * a j`), and `mapIdx`'s index shift, which needs the
  statement generalized over an offset — `mapIdx f (x :: xs)` recurses with `f (·+1)`.
  Verified on a concrete two-variable instance, so only the general induction is missing.
* `colCoeff cols names[j] row = Encoder.coeffOf (that row's form) j`, from the emitter's
  entries. Needs the variable-name `Nodup`, else another column's entries get summed in.
* Then `FormEqReal` follows from `sum_range_coeffAt` with `k = m.vars.size`, whose index
  bound is `WellFormed.FormDeclared`.

~~**4. `loBound`/`hiBound` recovery.**~~ **Done** — `loBound_flatten` and
`hiBound_flatten`. One wrinkle worth recording: the two halves are *not* symmetric. A
variable's own block always sets its lower bound, whatever the accumulator held, but a
continuous variable with no upper bound emits no upper entry at all, so `hiStep_foldl_own`
has to require the initial `none` where `loStep_foldl_own` is accumulator-agnostic. The
`Nodup` hypothesis is what supplies that `none`, by ruling out an earlier variable having
set it.

Then `mpsRoundTrip` is assembly. None of this is soundness-critical — see the file header.
-/

end LeanVIPR.Mps
