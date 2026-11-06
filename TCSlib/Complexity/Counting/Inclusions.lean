/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: a-gupte
-/
import TCSlib.Complexity.Counting.PolyTime
import TCSlib.Complexity.ClassNP.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# First facts about PP

`BPP ⊆ PP`, `NP ⊆ PP`, and `PP` is closed under complement [AB09, ch. 17], [FR99, §2]. The
complement and `NP` results go through gap functions (`Counting.inPP_iff_exists_isGapP`).

## Main definitions

None.

## Main results

* `Counting.InBPP.inPP` — `BPP ⊆ PP`, for every verifier model.
* `Counting.InPP.compl` — `PP` is closed under complement, for every verifier model with the gap
  closure properties.
* `Counting.inPP_polyTimeModel_compl` — the same for `Randomized.polyTimeModel`.
* `Counting.inPP_polyTimeModel_of_mem_NP` — `NP ⊆ PP`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [FR99] L. Fortnow, J. Rogers, *Complexity limitations on quantum computation*, Journal of
  Computer and System Sciences 59(2), 240–252, 1999.
-/

namespace Counting

open Randomized Complexity

variable {E : VerifierModel}

/-- **`BPP ⊆ PP`.** A `BPP` verifier is already a `PP` verifier: members are accepted with
probability at least `2/3 > 1/2`, and non-members with probability at most `1/3 ≤ 1/2`.
[AB09, ch. 17]

**Proof sketch.** Keep the verifier and the schedule. For `x ∈ L`, `Pr[accept] ≥ 2/3 > 1/2`.
For `x ∉ L`, `Pr[reject] ≥ 2/3`, so `Pr[accept] = 1 - Pr[reject] ≤ 1/3`
(`Randomized.randProb_bool_false`), which is not above `1/2`. -/
theorem InBPP.inPP {L : Language Bool} (h : InBPP E L) : InPP E L := by
  sorry

/-- **`PP` is closed under complement.** [AB09, ch. 17], [FR99, §2]

**Proof sketch.** By `inPP_iff_exists_isGapP`, take a gap function `f` with `x ∈ L ↔ 0 < f x`.
Then `g = 1 + (-f) + (-f) = 1 - 2f` is a gap function (`isGapP_one`, `IsGapP.neg`,
`IsGapP.add`), and for integers `0 < 1 - 2 f x ↔ f x ≤ 0 ↔ x ∉ L`. Apply
`inPP_iff_exists_isGapP` again. -/
theorem InPP.compl (hC : ClosedUnderCoinFill E) (hP : ClosedUnderPad E)
    (hN : ClosedUnderGapNeg E) (hS : ClosedUnderGapSum E) (hK : HasConstVerifiers E)
    {L : Language Bool} (h : InPP E L) : InPP E Lᶜ := by
  sorry

/-- `PP` is closed under complement in polynomial time.

**Proof sketch.** `InPP.compl` with the closure facts of `Counting/PolyTime.lean`. -/
theorem inPP_polyTimeModel_compl {L : Language Bool} (h : InPP polyTimeModel L) :
    InPP polyTimeModel Lᶜ := by
  sorry

/-- **`NP ⊆ PP`.** [AB09, ch. 17]

**Proof sketch.** Let `L ∈ NP` with verifier language `V ∈ P` and certificates of length exactly
`C · (|x| + 1)^c = polyLen C c |x|` (`Complexity.NP`). The certificate verifier has gap
`#cert(x)`, the number of certificates (`gap_certVerifier`, `polyTimeModel_eff_certVerifier`).
So `f = #cert + #cert + (-1) = 2 · #cert - 1` is a gap function (`IsGapP.add`,
`isGapP_neg_one`, with the closure facts of `Counting/PolyTime.lean`), and `0 < f x` iff some
certificate exists iff `x ∈ L`. Conclude with `inPP_iff_exists_isGapP`. -/
theorem inPP_polyTimeModel_of_mem_NP {L : Language Bool} (hL : L ∈ NP) :
    InPP polyTimeModel L := by
  sorry

/-- A concrete language in `PP` for polynomial time: the strings whose first bit is `true`. It
contains `[true]` and not `[]`, so it is neither `∅` nor everything (round-1 audit, sanity
statement 8).

**Proof sketch.** Use the verifier `M x r = x.headD false` with no random bits (`polyLen 0 0 = 0`):
its acceptance probability is `1` on members and `0` on the rest. It is efficient because its
accepting language `{pairEncode x r | x.headD false = true}` is the preimage under `pairFstD` of a
linear-time language, and its rejecting language is the complement (`preimage_mem_P`,
`compl_mem_P`). -/
theorem inPP_polyTimeModel_headD :
    InPP polyTimeModel ({x | x.headD false = true} : Language Bool) := by
  sorry

end Counting
