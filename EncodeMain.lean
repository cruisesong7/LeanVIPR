import LeanVIPRTactic

/-!
# `encode-mps` — run the encoder

`encodeMps` previously had no caller outside scratch files. This is it.

With no arguments it writes the knapsack's MPS to stdout. With a path it writes there and
compares against `examples/uns_knapsack.mps`, reporting the deviations — which are the
three deliberate ones recorded in `Impl/Encoder/Mps.lean` (one triple per line rather than
two pairs, bare integers rather than `n/1`, and `LO`/`UP` rather than `LI`/`UI`), not
errors.
-/

open LeanVIPR LeanVIPR.Impl.Encoder LeanVIPR.Tactic.Roundtrip

def main (args : List String) : IO UInt32 := do
  let text := encodeMpsNamed "k1" knapsack
  match args with
  | [] =>
      IO.print text
      return 0
  | [out] =>
      IO.FS.writeFile ⟨out⟩ text
      IO.println s!"wrote {out} ({text.length} bytes)"
      -- the preconditions are theorems, not runtime checks; say so
      IO.println "preconditions: WellFormed, EncodableNames, Emittable all proved by decide"
      IO.println "tokenization:  isTokenization_encodeMps' applies (knapsack_isTokenization)"
      return 0
  | _ =>
      IO.eprintln "Usage: encode-mps [<out.mps>]"
      return 1
