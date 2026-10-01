/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.Halting
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages

/-!
# Arora–Barak `UHALT`: an undecidable unary language in `P/poly`

## Main definitions

* `Nat.Partrec.Code.haltingSet` — the halting problem as a `Set ℕ`.
* `Language.uhalt` — AB's `UHALT`.

## Main results

* `Nat.Partrec.Code.not_computablePred_mem_haltingSet` — `haltingSet` is undecidable.
* `Language.not_computablePred_mem_unary` — `unary S` is undecidable when `S` is.
* `Language.uhalt_inPPoly` — `UHALT` is in `P/poly`.
* `Language.not_computablePred_mem_uhalt` — `UHALT` is undecidable.
* `Language.exists_le_allOnes_inPPoly_not_computablePred` — [AB09, p.110].

## Divergences from Arora–Barak p.110

AB writes `UHALT = {1ⁿ : n's binary expansion encodes a pair ⟨M, x⟩ such that M
halts on input x}`. The numbering is changed, the shape kept: `n` decodes to the
pair `(n.unpair.1, n.unpair.2)`, the first component read as a Gödel number
through `Denumerable.ofNat Nat.Partrec.Code`, the second as its input, and
"halts" is `Part.Dom` of `Nat.Partrec.Code.eval`. "Undecidable" is
`¬ ComputablePred (· ∈ L)`. `haltingSet` is a `Set ℕ`, not a language, so it
sits beside `Nat.Partrec.Code.eval` rather than in `Language`.

AB concludes `P ⊊ P/poly`. TCSlib has no machine model and no class `P`, and AB's
route to it also needs Theorem 6.6, deferred in `ch6/PLAN.md` (U5). Only the
statable half is here: `exists_le_allOnes_inPPoly_not_computablePred`.
The undecidability half is not reproved from AB: it is Mathlib's
`ComputablePred.halting_problem`, transported along the pairing.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Nat.Partrec.Code

/-- The halting problem as a set of naturals: `n` belongs when the code numbered
`n.unpair.1` halts on input `n.unpair.2`. -/
def haltingSet : Set ℕ :=
  {n | (eval (Denumerable.ofNat Code n.unpair.1) n.unpair.2).Dom}

/-- `haltingSet` is undecidable. -/
theorem not_computablePred_mem_haltingSet : ¬ ComputablePred (· ∈ haltingSet) := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  refine ComputablePred.halting_problem 0 (ComputablePred.computable_iff.mpr
    ⟨fun c => f (Nat.pair (Encodable.encode c) 0),
      hf.comp (Primrec₂.natPair.to_comp.comp Computable.encode (Computable.const 0)), ?_⟩)
  funext c
  have h₀ := congrFun hfe (Nat.pair (Encodable.encode c) 0)
  simpa [haltingSet, Nat.unpair_pair, Denumerable.ofNat_encode] using h₀

end Nat.Partrec.Code

namespace Language

/-- `unary S` is undecidable whenever `S` is. -/
theorem not_computablePred_mem_unary {S : Set ℕ} (hS : ¬ ComputablePred (· ∈ S)) :
    ¬ ComputablePred (· ∈ unary S) := by
  intro h
  obtain ⟨f, hf, hfe⟩ := ComputablePred.computable_iff.mp h
  have hrep : Computable fun n : ℕ => List.replicate n true :=
    ((Primrec.list_map Primrec.list_range (Primrec.const true).to₂).of_eq
      fun n => by simp).to_comp
  refine hS (ComputablePred.computable_iff.mpr
    ⟨fun n => f (List.replicate n true), hf.comp hrep, ?_⟩)
  funext n
  rw [← replicate_mem_unary_iff (S := S) n]
  exact congrFun hfe _

/-- `UHALT`: the words `1ⁿ` whose length codes a halting computation.
[AB09, p.110] -/
def uhalt : Language Bool := unary Nat.Partrec.Code.haltingSet

/-- `UHALT` is in `P/poly`. -/
theorem uhalt_inPPoly : uhalt.InPPoly := unary_inPPoly _

/-- `UHALT` is undecidable. -/
theorem not_computablePred_mem_uhalt : ¬ ComputablePred (· ∈ uhalt) :=
  not_computablePred_mem_unary Nat.Partrec.Code.not_computablePred_mem_haltingSet

/-- Some unary language is in `P/poly` and is not computable.  [AB09, p.110] -/
theorem exists_le_allOnes_inPPoly_not_computablePred :
    ∃ L : Language Bool, L ≤ allOnes ∧ L.InPPoly ∧ ¬ ComputablePred (· ∈ L) :=
  ⟨uhalt, unary_le_allOnes _, uhalt_inPPoly, not_computablePred_mem_uhalt⟩

end Language
