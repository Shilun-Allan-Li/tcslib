/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Complexity.Counting.GapP
import TCSlib.Complexity.Randomized.PolyTimeModel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The gap closure hypotheses hold in polynomial time

The theorems of `Counting/GapP.lean` and `Counting/Inclusions.lean` are stated for any verifier
model satisfying named closure hypotheses. This file states that the intended model,
`Randomized.polyTimeModel`, satisfies each of them, so that none of those theorems is vacuous.
It also introduces the certificate verifier of an `NP` language, the bridge used for
`NP ⊆ PP`.

The proofs are polynomial-time constructions (plan item Q0.7, fill epoch E3). Each one follows
the pattern of `Randomized.polyTimeModel_closedUnderRace`: the accepting and rejecting languages
of the new verifier are Boolean combinations of preimages, under polynomial-time maps on
`Turing.pairEncode x r`, of the old verifiers' languages. No new machine is built: the maps come
from the polynomial-time closure algebra (`Complexity.PolyTimeComputable.comp`, `pairFstD`,
`pairSndD`, `Randomized.sliceTake`, `Randomized.sliceDrop`), and the languages from
`Complexity.preimage_mem_P`, `inter_mem_P`, `union_mem_P` and `compl_mem_P` (plan §6).

## Main definitions

* `Counting.certVerifier V` — the gap verifier counting the certificates of `x` for the `NP`
  verifier language `V`.

## Main results

* `Counting.polyTimeModel_closedUnderGapNeg`, `_closedUnderPad`, `_closedUnderGapSum`,
  `_closedUnderGapProd`, `_hasConstVerifiers`, `_closedUnderCoinFill` — the closure hypotheses
  of `Counting/GapP.lean` hold for `Randomized.polyTimeModel`.
* `Counting.polyTimeModel_eff_certVerifier` — the certificate verifier of a `P` language is
  efficient.
* `Counting.gap_certVerifier` — its gap is the number of certificates.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [FR99] L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*, Journal of
  Computer and System Sciences 59(2), 240–252, 1999.
-/

namespace Counting

open Randomized Complexity Finset

/-- Polynomial time is closed under negating a verifier.

**Proof sketch.** If `V₁`, `V₀ ∈ P` are the accepting and rejecting languages of `M`, then `V₀`
and `V₁` are those of `negVerifier M`. -/
theorem polyTimeModel_closedUnderGapNeg : ClosedUnderGapNeg polyTimeModel := by
  sorry

/-- Polynomial time is closed under padding a verifier to a shifted polynomial schedule.

**Proof sketch.** The split point `polyLen a k |x| + c` is computable from `pairEncode x r` in
polynomial time, as in `Randomized.sliceTake` (which is the case `c = 0`). The accepting language
of `padVerifier M p` is the set of `pairEncode x r` whose tail after the split point is all
`false` (a `P` test on a polynomial-time image) and whose image `pairEncode x (r.take …)` lies in
`M`'s accepting language (`preimage_mem_P`); intersect (`inter_mem_P`). The same for rejection. -/
theorem polyTimeModel_closedUnderPad : ClosedUnderPad polyTimeModel := by
  sorry

/-- Polynomial time is closed under the sum of two verifiers.

**Proof sketch.** On `pairEncode x (b :: r')`, the accepting language is
`{b = true ∧ pairEncode x r' ∈ V₁¹} ∪ {b = false ∧ pairEncode x r' ∈ V₁²}`, a union of
intersections of preimages under the polynomial-time maps reading `b` and forming
`pairEncode x r'`; the same for rejection. The empty random string is in neither language. -/
theorem polyTimeModel_closedUnderGapSum : ClosedUnderGapSum polyTimeModel := by
  sorry

/-- Polynomial time is closed under the product of two verifiers at a polynomial split point.

**Proof sketch.** As for `Randomized.polyTimeModel_closedUnderRace`: with `sliceTake a k` and
`sliceDrop a k` giving the two halves, the accepting language is
`(pre V₁¹ ∩ pre V₁²) ∪ (pre V₀¹ ∩ pre V₀²)` and the rejecting language is
`(pre V₁¹ ∩ pre V₀²) ∪ (pre V₀¹ ∩ pre V₁²)`. -/
theorem polyTimeModel_closedUnderGapProd : ClosedUnderGapProd polyTimeModel := by
  sorry

/-- Polynomial time contains both constant verifiers.

**Proof sketch.** The accepting (or rejecting) language of `constVerifier b` is the set of
`pairEncode x r` with `r` all `false`, which is in `P` (`pairSndD` is polynomial-time and
"all bits `false`" is a linear-time test); the other language is empty (`empty_mem_P`). -/
theorem polyTimeModel_hasConstVerifiers : HasConstVerifiers polyTimeModel := by
  sorry

/-- Polynomial time is closed under resolving abstentions by a coin at a polynomial point.

**Proof sketch.** `coinFill M (polyLen a k)` accepts `pairEncode x r` iff `M` accepts the first
`polyLen a k |x|` bits, or `M` abstains on them and the next bit is `true`. With `sliceTake`,
that is `pre V₁ ∪ ((pre V₁)ᶜ ∩ (pre V₀)ᶜ ∩ {next bit is true})`, in `P` by the closure lemmas;
it rejects on the complement. -/
theorem polyTimeModel_closedUnderCoinFill : ClosedUnderCoinFill polyTimeModel := by
  sorry

open Classical in
/-- The *certificate verifier* of an `NP` verifier language `V`: on input `x` and candidate
certificate `u`, accept if `x ++ u ∈ V` and abstain otherwise. Its gap on length `m` is the number
of certificates of length `m` (`gap_certVerifier`). The verifier form follows
`Complexity.NP` [AB09, Def 2.1]. -/
noncomputable def certVerifier (V : Language Bool) : List Bool → List Bool → Option Bool :=
  fun x u => if x ++ u ∈ V then some true else none

open Classical in
/-- `certVerifier V` accepts `(x, u)` when `x ++ u ∈ V`, and abstains otherwise. -/
theorem certVerifier_eq (V : Language Bool) (x u : List Bool) :
    certVerifier V x u = if x ++ u ∈ V then some true else none := rfl

open Classical in
/-- The gap of the certificate verifier on length `m` is the number of certificates of length
`m`: strings `u` with `x ++ u ∈ V`.

**Proof sketch.** It never rejects, and it accepts exactly the certificates. -/
theorem gap_certVerifier (V : Language Bool) (m : ℕ) (x : List Bool) :
    gap (certVerifier V) m x =
      ((univ.filter fun u : Fin m → Bool => x ++ List.ofFn u ∈ V).card : ℤ) := by
  sorry

/-- The certificate verifier of a language in `P` is efficient.

**Proof sketch.** Its accepting language is the preimage of `V` under
`z ↦ pairFstD z ++ pairSndD z`, which is polynomial-time (`polyTimeComputable_pairFstD`,
`polyTimeComputable_pairSndD`, and concatenation), so it is in `P` (`preimage_mem_P`). Its
rejecting language is empty (`empty_mem_P`). -/
theorem polyTimeModel_eff_certVerifier {V : Language Bool} (hV : V ∈ P) :
    polyTimeModel.Eff (certVerifier V) := by
  sorry

end Counting
