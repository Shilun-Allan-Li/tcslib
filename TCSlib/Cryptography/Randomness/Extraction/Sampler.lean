/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Complexity.ClassP.BinaryArith.Basic
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import TCSlib.Cryptography.Randomness.Extraction.Rejection

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A bounded rejection sampler on consecutive coin blocks

The sampler used in [PS10, Theorem 183.6] reads a fixed number of blocks and returns the
first whose extractor output starts with `true`, using the last block as a fallback.
The security parameter at which the counterexample is needed is fixed before the sampler
is chosen, so fixed block widths and a constant coin polynomial suffice. The resulting
machine has no advice and is therefore uniform.

## Main definitions

* `RejectionSampler.chooseWord`: bounded first-success selection from a bit tape.
* `RejectionSampler.machine`: the uniform PPT implementing the selection.
* `RejectionSampler.coinEquiv`: its coins as a tape of exactly `(t + 1) * n` bits.

## Main results

* `RejectionSampler.chooseWord_poly`: fixed-width bounded selection is polynomial-time.
* `RejectionSampler.chooseWord_blocks`: its typed interpretation is `Rejection.select`.
* `RejectionSampler.machine_runAt_coinEquiv`: the machine implements that tape selection.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §8.3.2, Theorem 183.6.
-/

namespace TCSlib.Cryptography.Randomness.RejectionSampler

open Complexity Turing

/-- Trying `t` blocks of width `n` and falling back to block `t` means returning the first
block whose extractor output starts with `true`, or the final block if every test fails.
[PS10, Theorem 183.6]. Short input tapes are truncated by `List.take`. -/
def chooseWord (Ext : List Bool → List Bool) (n : ℕ) : ℕ → List Bool → List Bool
  | 0, r => r.take n
  | t + 1, r =>
      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n)

/-- With no trials, `chooseWord` returns the first `n` bits: `chooseWord Ext n 0 r = r.take n`.
-/
theorem chooseWord_zero (Ext : List Bool → List Bool) (n : ℕ) (r : List Bool) :
    chooseWord Ext n 0 r = r.take n := rfl

/-- One additional trial tests the first block, returning it on acceptance and otherwise
running the remaining trials on the tape with that block dropped. -/
theorem chooseWord_succ (Ext : List Bool → List Bool) (n t : ℕ) (r : List Bool) :
    chooseWord Ext n (t + 1) r =
      if (Ext (r.take n)).headD false then r.take n else chooseWord Ext n t (r.drop n) := rfl

/-- Taking any fixed number `n` of input bits is polynomial-time computable.

**Proof sketch.** Pair a constant unary word of length `n` with the input and apply the
published length-gated prefix machine. -/
theorem take_poly (n : ℕ) : PolyTimeComputable (fun r : List Bool => r.take n) := by
  have henc : PolyTimeComputable fun r => pairEncode (List.replicate n true) r :=
    (polyTimeComputable_const (List.replicate n true)).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_takePrefixByLength.comp henc
  convert h using 1
  funext r
  change r.take n = PrefixByLength.take (pairEncode (List.replicate n true) r)
  rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- If `Ext` is polynomial-time, the fixed-width sampler with any fixed number of trials is
polynomial-time. [PS10, Theorem 183.6, the efficiency claim].

**Proof sketch.** Induct on the fixed number of trials. The head-bit test composes the
extractor with a fixed prefix, and the conditional combinator joins that prefix with the
inductively constructed sampler on the fixed-width suffix. -/
theorem chooseWord_poly {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : PolyTimeComputable (chooseWord Ext n t) := by
  induction t with
  | zero =>
    convert take_poly n using 1
  | succ t ih =>
    have htest : PolyTimeComputable fun r => [(Ext (r.take n)).headD false] :=
      polyTimeComputable_headD.comp (hExt.comp (take_poly n))
    have h := polyTimeComputable_ite htest (take_poly n)
      (ih.comp (BinArith.polyTimeComputable_drop n))
    convert h using 1

/-- On a concatenated tuple of `n`-bit blocks, string selection encodes typed selection:
`chooseWord Ext n t (flatten (ofFn (ofFn ∘ x))) = ofFn (select D t x)`, where
`D a = (Ext (ofFn a)).headD false`.

**Proof sketch.** At each successor trial, `take n` reads the first encoded block and
`drop n` leaves the concatenation of the remaining blocks. Both selectors therefore make
the same branch choice; induction identifies the remaining trials. -/
theorem chooseWord_flatten (Ext : List Bool → List Bool) (n t : ℕ)
    (x : Fin (t + 1) → Fin n → Bool) :
    chooseWord Ext n t (List.ofFn fun i => List.ofFn (x i)).flatten =
      List.ofFn (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t x) := by
  induction t with
  | zero =>
    rw [Rejection.select_zero, List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.append_nil, chooseWord_zero]
    exact List.take_of_length_le (by simp only [List.length_ofFn, le_refl])
  | succ t ih =>
    have hflat : (List.ofFn fun i : Fin (t + 1 + 1) => List.ofFn (x i)).flatten =
        List.ofFn (x 0) ++ (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten := by
      rw [List.ofFn_succ, List.flatten_cons]
    have ht : (List.ofFn (x 0) ++
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).take n =
        List.ofFn (x 0) := List.take_left' List.length_ofFn
    have hd : (List.ofFn (x 0) ++
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten).drop n =
        (List.ofFn fun i : Fin (t + 1) => List.ofFn (x i.succ)).flatten :=
      List.drop_left' List.length_ofFn
    rw [hflat, chooseWord_succ, ht, hd, Rejection.select_succ]
    split_ifs
    · rfl
    · exact ih (fun i => x i.succ)

/-- On `(t + 1) * n` uniform coin bits, `chooseWord` encodes typed first-success selection
from the canonical `(t + 1)` blocks. This includes `n = 0`. -/
theorem chooseWord_blocks (Ext : List Bool → List Bool) (n t : ℕ)
    (r : Fin ((t + 1) * n) → Bool) :
    chooseWord Ext n t (List.ofFn r) =
      List.ofFn (Rejection.select (fun a : Fin n → Bool => (Ext (List.ofFn a)).headD false) t
        (FunFamily.blocks (t + 1) n r)) := by
  have h := FunFamily.ofFn_blocks_symm (t + 1) n (FunFamily.blocks (t + 1) n r)
  rw [Equiv.symm_apply_apply] at h
  rw [h]
  exact chooseWord_flatten Ext n t _

/-- The bounded rejection machine on `(t + 1) * n` coins has empty advice and runs
`chooseWord Ext n t` on its coin tape. [PS10, Theorem 183.6]. -/
noncomputable def machine {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : NUPPT :=
  NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
    (.const ((t + 1) * n))

/-- The defining equation of `machine` packages the polynomial-time coin function with
constant coin polynomial `(t + 1) * n` and empty advice. -/
theorem machine_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext) (n t : ℕ) :
    machine hExt n t =
      NUPPT.ofPolyTimeUniform ((chooseWord_poly hExt n t).comp polyTimeComputable_pairSndD)
        (.const ((t + 1) * n)) := rfl

/-- The bounded rejection machine is uniform: it has empty advice at every parameter. -/
theorem machine_uniform {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : (machine hExt n t).Uniform := by
  rw [machine_eq]
  exact NUPPT.ofPolyTimeUniform_uniform _ _

/-- The rejection machine's coin polynomial is the constant `(t + 1) * n`. -/
theorem machine_coins {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t : ℕ) : (machine hExt n t).coins = .const ((t + 1) * n) := by
  rw [machine_eq, NUPPT.coins_ofPolyTimeUniform]

/-- On an untyped coin tape `r`, at every activation parameter and argument, the rejection
machine returns `chooseWord Ext n t r`. -/
theorem machine_runAtL {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y r : List Bool) :
    (machine hExt n t).runAtL m y r = chooseWord Ext n t r := by
  rw [machine_eq, NUPPT.runAtL_ofPolyTimeUniform]
  change chooseWord Ext n t (pairSndD (pairEncode (pairEncode (NUPPT.advInput m y) []) r)) = _
  rw [pairSndD_pairEncode]

/-- On typed coins, the rejection machine runs `chooseWord` on the coin string. -/
theorem machine_runAt {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y : List Bool) (r : (machine hExt n t).Coins m) :
    (machine hExt n t).runAt m y r = chooseWord Ext n t (List.ofFn r) := by
  rw [NUPPT.runAt_eq, machine_runAtL]

/-- At every activation parameter, the rejection machine uses exactly `(t + 1) * n` bits. -/
theorem machine_coinLen {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : (machine hExt n t).coinLen m = (t + 1) * n := by
  rw [NUPPT.coinLen_eq, machine_coins, PolyExpr.eval_const]

/-- The rejection machine's coins are canonically the bit tape of length `(t + 1) * n`,
independently of its activation parameter. -/
noncomputable def coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : (machine hExt n t).Coins m ≃ (Fin ((t + 1) * n) → Bool) :=
  Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool)

/-- The canonical rejection-coin equivalence is the arrow equivalence induced by the
published equality `coinLen m = (t + 1) * n`. -/
theorem coinEquiv_eq {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) : coinEquiv hExt n t m =
      Equiv.arrowCongr (finCongr (machine_coinLen hExt n t m)) (Equiv.refl Bool) := rfl

/-- The canonical rejection-coin equivalence preserves the encoded coin string. -/
theorem coinEquiv_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (r : (machine hExt n t).Coins m) :
    List.ofFn (coinEquiv hExt n t m r) = List.ofFn r :=
  (List.ofFn_congr (machine_coinLen hExt n t m) r).symm

/-- The inverse canonical rejection-coin equivalence preserves the encoded coin string. -/
theorem coinEquiv_symm_ofFn {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (r : Fin ((t + 1) * n) → Bool) :
    List.ofFn ((coinEquiv hExt n t m).symm r) = List.ofFn r := by
  rw [← coinEquiv_ofFn hExt n t m, Equiv.apply_symm_apply]

/-- Running the rejection machine on a tape transported through `coinEquiv` is precisely
`chooseWord Ext n t` on that tape. -/
theorem machine_runAt_coinEquiv {Ext : List Bool → List Bool} (hExt : PolyTimeComputable Ext)
    (n t m : ℕ) (y : List Bool) (r : Fin ((t + 1) * n) → Bool) :
    (machine hExt n t).runAt m y ((coinEquiv hExt n t m).symm r) =
      chooseWord Ext n t (List.ofFn r) := by
  rw [machine_runAt, coinEquiv_symm_ofFn]

end TCSlib.Cryptography.Randomness.RejectionSampler
