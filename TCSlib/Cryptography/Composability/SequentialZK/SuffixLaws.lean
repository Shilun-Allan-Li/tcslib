/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
import TCSlib.Cryptography.Composability.SequentialZK.PrefixLaws

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Front-step and tape-independence readers for simulated suffixes

## Main definitions

This module introduces no definitions.

## Main results

* `phaseStep_eq_simStep` reads a phase update from a supplied typed simulator coin block.
* `phaseSuffix_front` separates the first update of a simulated suffix.
* `phaseSuffix_congr_blocks` shows that a suffix depends only on its own phase coin blocks.
* `phaseSuffix_update_before` ignores an overwritten table entry before its starting phase.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1 (sequential repetition of zero knowledge).
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity

/-- If global block `j` of `rS` equals `List.ofFn coin`, the normalized raw-tape update
`phaseStep` equals the typed update `simStep` on `coin`.
`phaseStep S k B verifierFirst x z rV rS j pre = simStep S x z rV (k.eval x.length) (B.eval
x.length) (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) j pre coin`. -/
theorem phaseStep_eq_simStep (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) (coin : S.Coins x.length)
    (hcoin : coinBlock (S.coinLen x.length) j rS = List.ofFn coin) :
    phaseStep S k B verifierFirst x z rV rS j pre =
      simStep S x z rV (k.eval x.length) (B.eval x.length)
        (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)
        j pre coin := by
  rw [phaseStep_eq, simStep_eq]
  dsimp only
  rw [hcoin, ← NUPPT.runAt_eq, ← NUPPT.simulate_eq]

/-- A suffix with `t+1` updates first applies phase `start` and then runs `t` updates from
`start+1`: `phaseSuffix … start pre (t+1) = phaseSuffix … (start+1)
(phaseStep … start pre) t`. -/
theorem phaseSuffix_front (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre : List (List Bool)) (t : ℕ) :
    phaseSuffix S k B verifierFirst x z rV rS start pre (t + 1) =
      phaseSuffix S k B verifierFirst x z rV rS (start + 1)
        (phaseStep S k B verifierFirst x z rV rS start pre) t := by
  induction t with
  | zero => rw [phaseSuffix_succ, phaseSuffix_zero, phaseSuffix_zero, Nat.add_zero]
  | succ t ih =>
    rw [phaseSuffix_succ, ih, phaseSuffix_succ]
    congr 1
    omega

/-- If two raw simulator tapes have equal coin blocks on `start≤j<start+t`, their
simulated suffixes from the same prefix are equal.

**Proof sketch.** Induct on the number of updates and use the published last-step suffix
reader. The induction hypothesis identifies the preceding prefixes. The last update reads
only its own coin block through the published phase-step reader, so the supplied last-block
equality identifies the final updates. -/
theorem phaseSuffix_congr_blocks (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS rS' : List Bool) (start : ℕ) (pre : List (List Bool)) (t : ℕ)
    (hblocks : ∀ j, start ≤ j → j < start + t →
      coinBlock (S.coinLen x.length) j rS = coinBlock (S.coinLen x.length) j rS') :
    phaseSuffix S k B verifierFirst x z rV rS start pre t =
      phaseSuffix S k B verifierFirst x z rV rS' start pre t := by
  induction t with
  | zero => rw [phaseSuffix_zero, phaseSuffix_zero]
  | succ t ih =>
    have hprevious := ih (fun j hlo hhi => hblocks j hlo (by omega))
    have hlast := hblocks (start + t) (by omega) (by omega)
    rw [phaseSuffix_succ, phaseSuffix_succ, hprevious, phaseStep_eq, phaseStep_eq]
    dsimp only
    rw [hlast]

/-- Overwriting simulator coin-table entry `i` before `start` does not change a suffix
whose indices lie within the table: for `i<start` and `start+t≤q`, `phaseSuffix` on
`List.ofFn ((FunFamily.blocks q c).symm (Function.update coins i fresh))` equals its value
on `List.ofFn ((FunFamily.blocks q c).symm coins)`, with `c=S.coinLen |x|`.

**Proof sketch.** Apply the suffix block-congruence reader. Each relevant block is a
canonical block-table projection. Its index is at least `start`, hence different from `i`,
so the public function-update reader leaves that entry unchanged. -/
theorem phaseSuffix_update_before (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV : List Bool) (q : ℕ) (coins : Fin q → S.Coins x.length)
    (i : Fin q) (fresh : S.Coins x.length) (start : ℕ) (pre : List (List Bool)) (t : ℕ)
    (hi : (i : ℕ) < start) (hend : start + t ≤ q) :
    phaseSuffix S k B verifierFirst x z rV
        (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm
          (Function.update coins i fresh))) start pre t =
      phaseSuffix S k B verifierFirst x z rV
        (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm coins)) start pre t := by
  have hread (F : Fin q → S.Coins x.length) (j : Fin q) :
      coinBlock (S.coinLen x.length) j
          (List.ofFn ((FunFamily.blocks q (S.coinLen x.length)).symm F)) =
        List.ofFn (F j) := by
    have hb := FunFamily.ofFn_blocks q (S.coinLen x.length)
      ((FunFamily.blocks q (S.coinLen x.length)).symm F) j
    rw [Equiv.apply_symm_apply] at hb
    exact (coinBlock_eq _ _ _).trans hb.symm
  apply phaseSuffix_congr_blocks
  intro j hlo hhi
  have hj : j < q := lt_of_lt_of_le hhi hend
  have hne : (⟨j, hj⟩ : Fin q) ≠ i := by
    intro he
    have hval := congrArg Fin.val he
    change j = (i : ℕ) at hval
    omega
  rw [hread _ ⟨j, hj⟩, hread _ ⟨j, hj⟩]
  exact congrArg List.ofFn (Function.update_of_ne hne fresh coins)

end TCSlib.Cryptography.SequentialZK
