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

end LeanVIPR.Mps
