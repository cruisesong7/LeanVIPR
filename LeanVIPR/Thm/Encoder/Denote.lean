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

/-! ## What is still open

Six of the nine obligations in `IsMpsToks` are discharged above: the decomposition, and
the `NAME`, `OBJSENSE`, `ROWS`, `RHS` and `BOUNDS` *syntax*. Three remain, and they are the
semantic ones — each relates a section's recovered contents back to `m`, rather than
saying which tokens derive which entries.

**1. `COLUMNS` syntax.** `IsSeq IsColEntry _ cols` for the `cols : List ColEntry` that
`columnsAux` emits. Needs a `colEntriesOf` analogous to `bndEntriesOf`, and a recursion
carrying the marker state, since `columnsAux` emits marker lines between columns.

**2. `DeclaresInt cols v.name ↔ v.isInt`.** The marker invariant: the `INTORG`/`INTEND`
pairs bracket exactly the integer variables. Needs a strengthened recursion hypothesis
relating `columnsAux`'s `inInt` argument to the run of variables already emitted — the
hardest of the four, because the property is about the *interleaving* rather than about
any one entry.

**3. `FormEqReal (rowForm cols names r.name) r.form`.** The transpose: `rowForm` rebuilds
a row from the column-major entries, and that must agree with `r.form` as a linear
function. The missing ingredient is a grouped-summation lemma over `ℝ`,

```
∀ f, (∀ t ∈ f, t.idx < k) → ∑_{j < k} (coeffOf f j) * a j = evalReal f a
```

`Thm/System/LinForm.lean` has `normForm_eval`, which is this statement over `Valuation`
(`ℚ`); a real-valued analogue is what is needed, plus the bookkeeping that `rowForm`'s
`if q = 0 then [] else _` skip does not change the sum. Requires `WellFormed.FormDeclared`
for the index bound and the variable-name `Nodup` so `colCoeff` does not pick up another
column's entries.

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
