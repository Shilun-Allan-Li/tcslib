/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.NewmanTheorem.FuncDisjointnessLowerBound.RectangleSwitching

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Disjointness lower bound: information terms and the chain rule

The information-theoretic half of the linear lower bound for disjointness
[RY20, Thm 6.13]. This file defines the special-coordinate information terms
`I(A_T : S | T A_{<T} B_{≥T} 𝒟)` and `I(B_T : S | T A_{≤T} B_{>T} 𝒟)` of [RY20, Ch. 6,
eq. (6.3)], shows that the Bob term is the Alice term of the dual protocol, and proves the
upper bound of eq. (6.3): each term is at most `ℓ · log 2 / n` for a protocol of
communication `ℓ`. The bound is obtained exactly as in the book: the chain-rule inequality
`Σ_i I(X_i : M | X_{<i} Y_{≥i}) ≤ I(X : M | Y)` [RY20, Lemma 6.15] is proved coordinate by
coordinate, the random special coordinate `T` is averaged out (it is uniform and independent
of the inputs under `𝒟`), and the resulting full-vector information is bounded by the
transcript entropy `H(M) ≤ ℓ · log 2`. Information is measured in nats throughout, hence the
`log 2` factors.

## Main definitions

* `aliceInfoTerm`, `bobInfoTerm`, `claimInfo`: Alice's and Bob's corrected special-coordinate
  information terms under the disjoint-conditioned law, and their sum.
* `fixedAliceInfoTerm`, `fixedAliceFullYInfoTerm`, `fixedAliceCrossInfoTerm`: the
  fixed-coordinate summands `I(X_i : M | X_{<i} Y_{≥i})`, `I(X_i : M | X_{<i} Y)` and
  `I(X_i : Y_{<i} | X_{<i} Y_{≥i})` of the chain-rule argument.

## Main results

* `aliceInfoTerm_dualProtocol_eq_bobInfoTerm`, `bobInfoTerm_dualProtocol_eq_aliceInfoTerm`,
  `claimInfo_dualProtocol`: protocol duality swaps the two information terms.
* `fixedAliceCrossInfoTerm_eq_zero`, `fixedAliceInfoTerm_le_fixedAliceFullYInfoTerm`,
  `sum_fixedAliceInfoTerm_le_xVector_info`: the chain-rule inequality [RY20, Lemma 6.15].
* `aliceInfoTerm_eq_average_fixedAliceInfoTerm`: averaging over the uniform special coordinate.
* `aliceInfoTerm_le_average_entropy_bound`, `bobInfoTerm_le_average_entropy_bound`,
  `claimInfo_le_average_info_upper`: the bound `ℓ · log 2 / n` of [RY20, Ch. 6, eq. (6.3)]
  and its two-sided sum `2 ℓ · log 2 / n`.

## References

* [RY20] A. Rao, A. Yehudayoff, *Communication Complexity and Applications*,
  Cambridge University Press, 2020.
* [Raz92] A. A. Razborov, "On the distributional complexity of disjointness",
  *Theoretical Computer Science* 106(2):385–390, 1992.
* [KS92] B. Kalyanasundaram, G. Schnitger, "The probabilistic communication complexity of
  set intersection", *SIAM J. Discrete Math.* 5(4):545–557, 1992.
* [BJKS04] Z. Bar-Yossef, T. S. Jayram, R. Kumar, D. Sivakumar, "An information statistics
  approach to data stream and communication complexity", *J. Comput. Syst. Sci.*
  68(4):702–732, 2004.

Original formalization by Lucy Horowitz, Timothe Kasriel, and Mihir Singhal.
-/

namespace CommunicationComplexity

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Functions.Disjointness

namespace RandomizedLowerBound

variable (n : ℕ+)

/-- Alice's corrected special-coordinate information term: the conditional mutual information
`I(X_T : M | T, X_<T, Y_≥T, D)` between Alice's special bit and the transcript, given the
special coordinate, Alice's bits before it and Bob's bits from it onward, under the hard
distribution conditioned on disjointness [RY20, Ch. 6, eq. (6.3)]
(`I(A_T : S | T A_{<T} B_{≥T} 𝒟)`). -/
noncomputable def aliceInfoTerm
    (p : ProtocolType n) : ℝ :=
  I[specialX n : message n p | aliceClaimConditioning n ; disjointCondMeasure n]

/-- Bob's corrected special-coordinate information term: the conditional mutual information
`I(Y_T : M | T, X_≤T, Y_>T, D)` between Bob's special bit and the transcript, given the
special coordinate, Alice's bits up to it and Bob's bits after it, under the hard
distribution conditioned on disjointness; the Bob mirror of the term in
[RY20, Ch. 6, eq. (6.3)]. -/
noncomputable def bobInfoTerm
    (p : ProtocolType n) : ℝ :=
  I[specialY n : message n p | bobClaimConditioning n ; disjointCondMeasure n]

/-- The total corrected special-coordinate information: the sum of Alice's and Bob's
corrected information terms. This is the quantity the headline argument shows is at least
a fixed positive constant for any protocol of error `≤ 1/32` (`Headline.lean`) and at most
`2 ℓ · log 2 / n` for a protocol of communication `ℓ` [RY20, Ch. 6, eq. (6.3)]. Deviation:
the book bounds the two sides separately and picks the larger WLOG; the formalisation sums
them so that no case split is needed. -/
noncomputable def claimInfo
    (p : ProtocolType n) : ℝ :=
  aliceInfoTerm n p + bobInfoTerm n p

open Classical in
/-- Bob's corrected information term is nonnegative, as any conditional mutual information
is. -/
theorem bobInfoTerm_nonneg
    (p : ProtocolType n) :
    0 ≤ bobInfoTerm n p := by
  rw [bobInfoTerm]
  exact ProbabilityTheory.condMutualInfo_nonneg
    (μ := disjointCondMeasure n)
    (X := specialY n) (Y := message n p) (Z := bobClaimConditioning n)
    Measurable.of_discrete Measurable.of_discrete

/-- Alice's corrected information term is at most the total corrected information
`claimInfo`, since the Bob term it is missing is nonnegative. -/
theorem aliceInfoTerm_le_claimInfo
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤ claimInfo n p := by
  rw [claimInfo]
  linarith [bobInfoTerm_nonneg n p]

open Classical in
/-- Shared engine for the special-coordinate information dualities: a conditional mutual
information between a special bit `X'`, the dual protocol's transcript and a conditioning `Z'`,
all under the disjoint-conditioned measure, equals the corresponding quantity for the original
protocol with bit `X` and conditioning `Z`, provided `X'` and `Z'` on the dual sample are `X`
and the recoded `Z` on the original sample.

**Proof sketch.** Step 1: the sample-space duality preserves the disjoint-conditioned law.
Step 2: hence the dual-side information equals the information of the three variables
pulled back along the duality. Step 3: the transcript of the dual protocol and the
conditioning recoding are injective functions of the original transcript and conditioning,
so the recoded information equals the original one. Step 4: the pulled-back variables are
exactly the recoded originals (by the two hypotheses and
`message_dualProtocol_dualHardSample`), which closes the chain. -/
private theorem condMutualInfo_message_dualProtocol_eq
    (p : ProtocolType n)
    {X X' : HardSample n → Bool}
    {Z Z' : HardSample n → Fin n × (Fin n → Bool) × (Fin n → Bool)}
    (hX : ∀ ω, X' (dualHardSample n ω) = X ω)
    (hZ : ∀ ω, Z' (dualHardSample n ω) = dualConditioningValue n (Z ω)) :
    I[X' : message n (dualProtocol n p) | Z' ; disjointCondMeasure n] =
      I[X : message n p | Z ; disjointCondMeasure n] := by
  -- Step 1: hard-sample duality preserves the disjoint-conditioned measure.
  have hmap : MeasurePreserving (dualHardSample n) (disjointCondMeasure n)
      (disjointCondMeasure n) :=
    disjointCondMeasure_measurePreserving_dualHardSample n
  -- Step 2: pull the dual-side information back along the duality.
  have hpull :
      I[X' : message n (dualProtocol n p) | Z' ; disjointCondMeasure n] =
        I[fun ω => X' (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => Z' (dualHardSample n ω) ; disjointCondMeasure n] :=
    ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := disjointCondMeasure n) (μ' := disjointCondMeasure n)
      (X := X') (Y := message n (dualProtocol n p)) (Z := Z')
      (X' := fun ω => X' (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => Z' (dualHardSample n ω))
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω => (X' ω, message n (dualProtocol n p) ω, Z' ω))
        Measurable.of_discrete)
  -- Step 3: injective recodings of the transcript and the conditioning do not change the
  -- information.
  have hrec :
      I[X : (fun ω => dualProtocolTranscriptMap n p (message n p ω)) |
          (fun ω => dualConditioningValue n (Z ω)) ; disjointCondMeasure n] =
        I[X : message n p | Z ; disjointCondMeasure n] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_comp_right_conditioning_of_injective
        (μ := disjointCondMeasure n) (X := X) (Y := message n p) (Z := Z)
        (f := dualProtocolTranscriptMap n p) (g := dualConditioningValue n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
        Measurable.of_discrete Measurable.of_discrete
        (dualProtocolTranscriptMap_injective n p) (dualConditioningValue_injective n)
  -- Step 4: the pulled-back variables are the recoded originals.
  rw [hpull]
  simpa [hX, message_dualProtocol_dualHardSample, hZ] using hrec

open Classical in
/-- Alice's corrected information term for the dual protocol equals Bob's corrected
information term for the original protocol. This is the formal content of the 'WLOG' step in
the proof of [RY20, Thm 6.13] (the 'WLOG' step leading to eq. (6.2)): the Bob-side case of the
argument is the Alice-side case applied to the dual protocol. The proof instantiates the
private duality engine `condMutualInfo_message_dualProtocol_eq` with the identities
`X_T ∘ dual = Y_T` and `(T, X_<T, Y_≥T) ∘ dual = recoded (T, X_≤T, Y_>T)`. -/
theorem aliceInfoTerm_dualProtocol_eq_bobInfoTerm
    (p : ProtocolType n) :
    aliceInfoTerm n (dualProtocol n p) = bobInfoTerm n p := by
  -- Step 1: instantiate the shared duality engine with Alice's dual bit/conditioning identities.
  rw [aliceInfoTerm, bobInfoTerm]
  exact condMutualInfo_message_dualProtocol_eq n p (specialX_dualHardSample n)
    (aliceClaimConditioning_dualHardSample n)

open Classical in
/-- Bob's corrected information term for the dual protocol equals Alice's corrected
information term for the original protocol; the mirror image of
`aliceInfoTerm_dualProtocol_eq_bobInfoTerm`, again the 'WLOG' step leading to eq. (6.2) in the
proof of [RY20, Thm 6.13]. The proof instantiates the same private duality engine with the
identities `Y_T ∘ dual = X_T` and `(T, X_≤T, Y_>T) ∘ dual = recoded (T, X_<T, Y_≥T)`. -/
theorem bobInfoTerm_dualProtocol_eq_aliceInfoTerm
    (p : ProtocolType n) :
    bobInfoTerm n (dualProtocol n p) = aliceInfoTerm n p := by
  -- Step 1: instantiate the shared duality engine with Bob's dual bit/conditioning identities.
  rw [bobInfoTerm, aliceInfoTerm]
  exact condMutualInfo_message_dualProtocol_eq n p (specialY_dualHardSample n)
    (bobClaimConditioning_dualHardSample n)

open Classical in
/-- The information `I(X : M' | Y)` between Alice's full input vector and the transcript of
the dual protocol, given Bob's full vector, equals the information `I(Y : M | X)` between
Bob's full vector and the transcript of the original protocol, given Alice's vector, both
under the disjoint-conditioned law. This transports the full-vector bound of
[RY20, Lemma 6.15] between the two sides.

**Proof sketch.** The same pull-back/recoding argument as for the special-coordinate terms,
but with the whole input vectors, so the recodings are the coordinate reversals. Step 1: the
sample-space duality preserves the disjoint-conditioned law, so the dual-side information
equals the information of `(X, M', Y)` pulled back along the duality. Step 2: reversing the
coordinates of both vectors and transporting the transcript are injective recodings of
`(Y, M, X)`, so the recoded information equals `I(Y : M | X)`. Step 3: the pulled-back
variables are exactly these recodings (`xVector_dualHardSample`, `yVector_dualHardSample`,
`message_dualProtocol_dualHardSample`). -/
theorem xVector_message_info_dualProtocol_eq_yVector_message_info
    (p : ProtocolType n) :
    I[xVector n : message n (dualProtocol n p) | yVector n ; disjointCondMeasure n] =
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  -- Step 1: duality preserves the law; pull the dual-side information back along it.
  have hmap : MeasurePreserving (dualHardSample n) μ μ := by
    simpa [μ] using disjointCondMeasure_measurePreserving_dualHardSample n
  have hpull :
      I[xVector n : message n (dualProtocol n p) | yVector n ; μ] =
        I[fun ω => xVector n (dualHardSample n ω) :
          fun ω => message n (dualProtocol n p) (dualHardSample n ω) |
          fun ω => yVector n (dualHardSample n ω) ; μ] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := μ)
      (X := xVector n) (Y := message n (dualProtocol n p)) (Z := yVector n)
      (X' := fun ω => xVector n (dualHardSample n ω))
      (Y' := fun ω => message n (dualProtocol n p) (dualHardSample n ω))
      (Z' := fun ω => yVector n (dualHardSample n ω))
      (identDistrib_self_comp_measurePreserving hmap
        (fun ω => (xVector n ω, message n (dualProtocol n p) ω, yVector n ω))
        Measurable.of_discrete)
  rw [show disjointCondMeasure n = μ by rfl, hpull]
  -- Step 2: coordinate reversal and transcript transport are injective recodings of `(Y, M, X)`.
  have hrec :
      I[(fun ω => reverseBoolVector n (yVector n ω)) :
          (fun ω => dualProtocolTranscriptMap n p (message n p ω)) |
          (fun ω => reverseBoolVector n (xVector n ω)) ; μ] =
        I[yVector n : message n p | xVector n ; μ] := by
    simpa [Function.comp_def] using
      ProbabilityTheory.condMutualInfo_of_inj'
        (X := yVector n) (Y := message n p) (Z := xVector n)
        Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete μ
        (reverseBoolVector_injective n) (dualProtocolTranscriptMap_injective n p)
        (reverseBoolVector_injective n)
  -- Step 3: the pulled-back variables are exactly these recodings.
  simpa [μ, xVector_dualHardSample, yVector_dualHardSample,
    message_dualProtocol_dualHardSample] using hrec

open Classical in
/-- The total corrected information `claimInfo` is invariant under protocol duality: the dual
protocol has the same `claimInfo` as the original, because duality swaps the Alice and Bob
terms. This is what makes the 'WLOG' step leading to eq. (6.2) in the proof of [RY20, Thm 6.13]
available for the Bob-side case. -/
theorem claimInfo_dualProtocol
    (p : ProtocolType n) :
    claimInfo n (dualProtocol n p) = claimInfo n p := by
  rw [claimInfo, aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    bobInfoTerm_dualProtocol_eq_aliceInfoTerm, claimInfo, add_comm]

open Classical in
/-- The fixed-coordinate summand `I(X_i : M | X_<i, Y_≥i)` of the chain-rule inequality: the
conditional mutual information, under the disjoint-conditioned law, between Alice's bit at
the fixed coordinate `i` and the transcript, given Alice's bits before `i` and Bob's bits
from `i` onward [RY20, Lemma 6.15] (the left-hand summand
`I(X_i : M | X_{<i} Y_{≥i})`). -/
noncomputable def fixedAliceInfoTerm
    (p : ProtocolType n)
    (i : Fin n) : ℝ :=
  I[fixedXBit n i : message n p | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- The fixed-coordinate term `I(X_i : M | X_<i, Y)` with Bob's full vector in the
conditioning: the conditional mutual information, under the disjoint-conditioned law,
between Alice's bit at `i` and the transcript, given Alice's bits before `i` and all of
Bob's bits [RY20, Lemma 6.15] (the summand `I(X_i : M | X_{<i} Y)` of the proof, whose sum
over `i` is `I(X : M | Y)` by the chain rule). -/
noncomputable def fixedAliceFullYInfoTerm
    (p : ProtocolType n)
    (i : Fin n) : ℝ :=
  I[fixedXBit n i : message n p | fixedAliceFullYConditioning n i ; disjointCondMeasure n]

open Classical in
/-- The cross-information term `I(X_i : Y_<i | X_<i, Y_≥i)` under the disjoint-conditioned
law: the conditional mutual information between Alice's bit at `i` and Bob's bits before `i`,
given Alice's bits before `i` and Bob's bits from `i` onward. It vanishes
(`fixedAliceCrossInfoTerm_eq_zero`), which is the independence input of
[RY20, Lemma 6.15] (`I(X_i : Y_{<i} | X_{<i} Y_{≥i}) = 0`). -/
noncomputable def fixedAliceCrossInfoTerm (i : Fin n) : ℝ :=
  I[fixedXBit n i : fixedYBefore n i | fixedAliceConditioning n i ; disjointCondMeasure n]

open Classical in
/-- Under the hard distribution conditioned on disjointness, Alice's bit at a fixed
coordinate `i` carries no information about Bob's earlier bits once Alice's earlier bits and
Bob's later bits are given: `I(X_i : Y_<i | X_<i, Y_≥i, D) = 0`. This is the
independence hypothesis of [RY20, Lemma 6.15] (the pairs `(X_j, Y_j)` are independent under
`𝒟`), in the form used by the chain-rule step. The proof transports the triple to the
coordinate-vector model, where the law is the uniform disjoint-vector law, and applies the
independence result proved there. -/
theorem fixedAliceCrossInfoTerm_eq_zero (i : Fin n) :
    fixedAliceCrossInfoTerm n i = 0 := by
  rw [fixedAliceCrossInfoTerm]
  let ν := uniformDisjointCoordinateVector n
  have hpull :
      I[fixedXBit n i : fixedYBefore n i | fixedAliceConditioning n i ; disjointCondMeasure n] =
        I[coordinateXBit n i : coordinateYBefore n i | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := disjointCondMeasure n) (μ' := ν)
      (X := fixedXBit n i) (Y := fixedYBefore n i) (Z := fixedAliceConditioning n i)
      (X' := coordinateXBit n i)
      (Y' := coordinateYBefore n i)
      (Z' := coordinateAliceConditioning n i)
      (by simpa [ν] using identDistrib_fixedAliceCrossInfoTriple_uniform n i)
  rw [hpull]
  exact uniformDisjointCoordinateVector_crossInfo_eq_zero n i

open Classical in
/-- The fixed-coordinate chain-rule inequality: for every coordinate `i`, Alice's summand
with Bob's suffix in the conditioning is at most the summand with Bob's full vector in the
conditioning, `I(X_i : M | X_<i, Y_≥i, D) ≤ I(X_i : M | X_<i, Y, D)`
[RY20, Lemma 6.15] (the single-coordinate step of the displayed chain).

**Proof sketch.** Write `A = (X_<i, Y_≥i)` for the conditioning. Step 1: adding Bob's
earlier bits `Y_<i` to the transcript can only increase information,
`I(X_i : M | A) ≤ I(X_i : (Y_<i, M) | A)`. Step 2: by the chain rule the right-hand side is
`I(X_i : Y_<i | A) + I(X_i : M | (Y_<i, A))`. Step 3: the first summand is the cross term
`I(X_i : Y_<i | X_<i, Y_≥i)`, which vanishes by `fixedAliceCrossInfoTerm_eq_zero`. Step 4:
the conditioning `(Y_<i, A) = (Y_<i, X_<i, Y_≥i)` is an injective recoding of `(X_<i, Y)`,
so the second summand is `I(X_i : M | X_<i, Y)`. The final `calc` chains the three
identities. -/
theorem fixedAliceInfoTerm_le_fixedAliceFullYInfoTerm
    (p : ProtocolType n)
    (i : Fin n) :
    fixedAliceInfoTerm n p i ≤ fixedAliceFullYInfoTerm n p i := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let Xᵢ : HardSample n → Bool := fixedXBit n i
  let M : HardSample n → TranscriptType n p := message n p
  let Ypre : HardSample n → Fin n → Bool := fixedYBefore n i
  let A : HardSample n → (Fin n → Bool) × (Fin n → Bool) :=
    fixedAliceConditioning n i
  -- Step 1: adjoining `Y_<i` to the transcript can only increase the information.
  have hle_add :
      I[Xᵢ : M | A ; μ] ≤ I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] := by
    exact ProbabilityTheory.condMutualInfo_le_prod_right_snd
      (μ := μ) (X := Xᵢ) (Y := Ypre) (W := M) (Z := A)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete
  -- Step 2: chain rule on the pair `(Y_<i, M)`.
  have hchain :
      I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] =
        I[Xᵢ : Ypre | A ; μ] + I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] := by
    exact ProbabilityTheory.condMutualInfo_prod_right_eq_add
      (μ := μ) (X := Xᵢ) (Y := Ypre) (W := M) (Z := A)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      Measurable.of_discrete
  -- Step 3: the cross term `I(X_i : Y_<i | X_<i, Y_≥i)` vanishes.
  have hcross : I[Xᵢ : Ypre | A ; μ] = 0 := by
    simpa [fixedAliceCrossInfoTerm, μ, Xᵢ, Ypre, A] using
      fixedAliceCrossInfoTerm_eq_zero n i
  -- Step 4: `(Y_<i, X_<i, Y_≥i)` is an injective recoding of `(X_<i, Y)`.
  have hrec :
      I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] =
        I[Xᵢ : M | fixedAliceFullYConditioning n i ; μ] := by
    have h := ProbabilityTheory.condMutualInfo_of_inj
      (μ := μ) (X := Xᵢ) (Y := M) (Z := fixedAliceFullYConditioning n i)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
      (fixedAliceChainConditioningValue_injective n i)
    rw [fixedAliceChainConditioningValue_fixedAliceFullYConditioning] at h
    simpa [Function.comp_def, Xᵢ, M, Ypre, A] using h
  rw [fixedAliceInfoTerm, fixedAliceFullYInfoTerm]
  calc
    I[fixedXBit n i : message n p | fixedAliceConditioning n i ; disjointCondMeasure n]
        ≤ I[Xᵢ : (fun ω => (Ypre ω, M ω)) | A ; μ] := by
          simpa [μ, Xᵢ, M, A] using hle_add
    _ = I[Xᵢ : Ypre | A ; μ] + I[Xᵢ : M | (fun ω => (Ypre ω, A ω)) ; μ] :=
          hchain
    _ = I[fixedXBit n i : message n p | fixedAliceFullYConditioning n i ;
            disjointCondMeasure n] := by
          rw [hcross, zero_add, hrec]

open Classical in
/-- Summed over all coordinates, Alice's summands with Bob's suffix in the conditioning are
at most the summands with Bob's full vector in the conditioning:
`Σ_i I(X_i : M | X_<i, Y_≥i, D) ≤ Σ_i I(X_i : M | X_<i, Y, D)` [RY20, Lemma 6.15] (the
inequality of the displayed chain, before the chain rule collapses the right-hand side). -/
theorem sum_fixedAliceInfoTerm_le_sum_fixedAliceFullYInfoTerm
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceInfoTerm n p i) ≤
      ∑ i : Fin n, fixedAliceFullYInfoTerm n p i := by
  exact Finset.sum_le_sum fun i _ => fixedAliceInfoTerm_le_fixedAliceFullYInfoTerm n p i

open Classical in
/-- The chain rule for Alice's full input vector: the sum over `i` of the fixed-coordinate
terms with Bob's full vector in the conditioning is the full-vector information,
`Σ_i I(X_i : M | X_<i, Y, D) = I(X : M | Y, D)` [RY20, Lemma 6.15] (the final equality of
the displayed chain). The proof is the iterated chain rule
`condMutualInfo_boolVector_eq_sum_strictPrefix` plus unfolding the strict-prefix
conditioning to `fixedAliceFullYConditioning`. -/
theorem sum_fixedAliceFullYInfoTerm_eq_xVector_info
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceFullYInfoTerm n p i) =
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] := by
  have hchain := ProbabilityTheory.condMutualInfo_boolVector_eq_sum_strictPrefix
    (μ := disjointCondMeasure n) (X := xVector n) (Y := message n p) (Z := yVector n)
    Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete
  rw [hchain]
  apply Finset.sum_congr rfl
  intro i _hi
  unfold fixedAliceFullYInfoTerm fixedAliceFullYConditioning fixedXStrictPrefix fixedXBit xVector
    ProbabilityTheory.boolVectorStrictPrefix
  rfl

open Classical in
/-- The chain-rule inequality for Alice's summands: the sum over all coordinates of
`I(X_i : M | X_<i, Y_≥i, D)` is at most the full-vector information `I(X : M | Y, D)`
[RY20, Lemma 6.15] (first inequality, for the law `p(ab | 𝒟)`).

Its only probabilistic input is `fixedAliceCrossInfoTerm_eq_zero`. -/
theorem sum_fixedAliceInfoTerm_le_xVector_info
    (p : ProtocolType n) :
    (∑ i : Fin n, fixedAliceInfoTerm n p i) ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] := by
  calc
    (∑ i : Fin n, fixedAliceInfoTerm n p i)
        ≤ ∑ i : Fin n, fixedAliceFullYInfoTerm n p i :=
          sum_fixedAliceInfoTerm_le_sum_fixedAliceFullYInfoTerm n p
    _ = I[xVector n : message n p | yVector n ; disjointCondMeasure n] :=
          sum_fixedAliceFullYInfoTerm_eq_xVector_info n p

open Classical in
/-- Alice's corrected information term is the average, over the uniformly distributed special
coordinate `T = i`, of the information `I(X_T : M | X_<T, Y_≥T)` computed under the
disjoint-conditioned law further conditioned on `T = i`: each fiber is weighted by
`Pr[T = i | D] = 1/n`. This splits the conditioning `(T, X_<T, Y_≥T)` into `T` and the
remaining dynamic data, using that conditioning on a product variable is a weighted sum of
conditionings on its first component. -/
theorem aliceInfoTerm_eq_sum_specialCoordinate_fiber_info
    (p : ProtocolType n) :
    aliceInfoTerm n p =
      ∑ i : Fin n,
        (1 / (n : ℝ) : ℝ) *
          I[specialX n : message n p | aliceDynamicConditioning n ;
            (disjointCondMeasure n)[|specialCoordinate n ← i]] := by
  rw [aliceInfoTerm, aliceClaimConditioning_eq_specialCoordinate_prod_dynamic]
  rw [ProbabilityTheory.condMutualInfo_prod_conditioning_eq_sum
    (μ := disjointCondMeasure n)
    (X := specialX n) (Y := message n p)
    (K := specialCoordinate n) (Z := aliceDynamicConditioning n)
    Measurable.of_discrete Measurable.of_discrete]
  simp_rw [disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton]

open Classical in
/-- After conditioning the disjoint-conditioned law on the special coordinate `T = i`, the
information `I(X_T : M | X_<T, Y_≥T)` between Alice's special bit and the transcript equals
the fixed-coordinate summand `I(X_i : M | X_<i, Y_≥i, D)` computed under the
disjoint-conditioned law without any conditioning on `T`. This is the formal content of
'conditioned on `𝒟`, `T` is independent of `A, B`' [RY20, Ch. 6, eq. (6.3)]: the fiber
`T = i` sees the same input law as the whole space.

**Proof sketch.** Write `μ` for the disjoint-conditioned law, `μᵢ` for `μ` conditioned on
`T = i`, and `ν` for the uniform law on disjoint coordinate vectors. Both sides are shown to
equal the information `I(X_i : M | X_<i, Y_≥i)` of the coordinate-vector model under `ν`.
Step 1: `μᵢ` is a probability measure, since `T = i` has mass `1/n` under `μ`. Step 2:
almost surely under `μᵢ` the special bit `X_T` is the fixed bit `X_i`, and hence (as `μᵢ` is
absolutely continuous with respect to `μ`) the coordinate-vector bit at `i`; likewise the
transcript and the dynamic conditioning `(X_<T, Y_≥T)` are a.s. their coordinate-vector
counterparts at `i`. Step 3: hence the left-hand side equals the information of the
coordinate-vector triple under `μᵢ`, and, because the generated coordinate vector is
`ν`-distributed under `μᵢ` (`T` is independent of the vector under `𝒟`), this is the
information under `ν`. Step 4: the same two moves for the right-hand side: the fixed-
coordinate triple is a.s. the coordinate-vector triple under `μ`, and the generated vector is
`ν`-distributed under `μ`. Step 5: chain the two identities. -/
theorem aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm
    (p : ProtocolType n) (i : Fin n) :
    I[specialX n : message n p | aliceDynamicConditioning n ;
      (disjointCondMeasure n)[|specialCoordinate n ← i]] =
      fixedAliceInfoTerm n p i := by
  let μ : Measure (HardSample n) := disjointCondMeasure n
  let μi : Measure (HardSample n) := μ[|specialCoordinate n ← i]
  let ν : Measure (Fin n → DisjointCoordinate) :=
    uniformDisjointCoordinateVector n
  -- Step 1: `μᵢ` is a probability measure because `T = i` has positive mass under `μ`.
  haveI : IsProbabilityMeasure μi := by
    dsimp [μi, μ]
    apply ProbabilityTheory.cond_isProbabilityMeasure
    rw [← MeasureTheory.measureReal_ne_zero_iff]
    rw [disjointCondMeasure_measureReal_specialCoordinate_preimage_singleton]
    positivity
  -- Step 2: under `μᵢ`, the special-coordinate variables are a.s. the fixed-coordinate ones,
  -- hence a.s. their coordinate-vector counterparts at `i`.
  have hspecial_fixed : specialX n =ᵐ[μi] fixedXBit n i := by
    dsimp [μi, μ]
    filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
    have hT : ω.T = i := by
      simpa [specialCoordinate] using hω
    simp [specialX, fixedXBit, xBit, hT]
  have hspecial_coord :
      specialX n =ᵐ[μi]
        fun ω => coordinateXBit n i (disjointCoordinateVector n ω) := by
    exact hspecial_fixed.trans
      (by
        simpa [μi, μ] using
          (cond_absolutelyContinuous.ae_le (fixedXBit_ae_eq_coordinateXBit n i)))
  have hmessage_coord_cond :
      message n p =ᵐ[μi]
        fun ω => coordinateMessage n p (disjointCoordinateVector n ω) := by
    simpa [μi, μ] using
      (cond_absolutelyContinuous.ae_le (message_ae_eq_coordinateMessage n p))
  have hdyn_fixed :
      aliceDynamicConditioning n =ᵐ[μi] fixedAliceConditioning n i := by
    dsimp [μi, μ]
    filter_upwards [ae_cond_mem MeasurableSet.of_discrete] with ω hω
    have hT : ω.T = i := by
      simpa [specialCoordinate] using hω
    ext j <;>
      simp [aliceDynamicConditioning, fixedAliceConditioning, xBeforeSpecial,
        yGeSpecial, fixedXBefore, fixedYGe, hT]
  have hdyn_coord :
      aliceDynamicConditioning n =ᵐ[μi]
        fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω) := by
    exact hdyn_fixed.trans
      (by
        simpa [μi, μ] using
          (cond_absolutelyContinuous.ae_le
            (fixedAliceConditioning_ae_eq_coordinateAliceConditioning n i)))
  -- Step 3: the left-hand side is the coordinate-vector information under `μᵢ`, which is the
  -- information under `ν` since the generated vector is `ν`-distributed given `T = i`.
  have hleft_congr :
      I[specialX n : message n p | aliceDynamicConditioning n ; μi] =
        I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μi] := by
    exact ProbabilityTheory.condMutualInfo_congr_ae_finite
      (μ := μi)
      (X := specialX n) (Y := message n p) (Z := aliceDynamicConditioning n)
      (X' := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y' := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z' := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      hspecial_coord hmessage_coord_cond hdyn_coord
  have hleft_pull :
      I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μi] =
        I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μi) (μ' := ν)
      (X := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (X' := coordinateXBit n i)
      (Y' := coordinateMessage n p)
      (Z' := coordinateAliceConditioning n i)
      (by
        simpa [Function.comp_def, μi, μ, ν] using
          (identDistrib_disjointCoordinateVector_uniform_cond_specialCoordinate n i).comp
            (Measurable.of_discrete
            (f := fun coords =>
              (coordinateXBit n i coords, coordinateMessage n p coords,
                coordinateAliceConditioning n i coords))))
  -- Step 4: the right-hand side is the coordinate-vector information under `μ`, which is
  -- again the information under `ν`.
  have hright_congr :
      fixedAliceInfoTerm n p i =
        I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μ] := by
    rw [fixedAliceInfoTerm]
    exact ProbabilityTheory.condMutualInfo_congr_ae_finite
      (μ := μ)
      (X := fixedXBit n i) (Y := message n p) (Z := fixedAliceConditioning n i)
      (X' := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y' := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z' := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (fixedXBit_ae_eq_coordinateXBit n i)
      (message_ae_eq_coordinateMessage n p)
      (fixedAliceConditioning_ae_eq_coordinateAliceConditioning n i)
  have hright_pull :
      I[(fun ω => coordinateXBit n i (disjointCoordinateVector n ω)) :
          (fun ω => coordinateMessage n p (disjointCoordinateVector n ω)) |
          (fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω)) ; μ] =
        I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] := by
    exact ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite
      (μ := μ) (μ' := ν)
      (X := fun ω => coordinateXBit n i (disjointCoordinateVector n ω))
      (Y := fun ω => coordinateMessage n p (disjointCoordinateVector n ω))
      (Z := fun ω => coordinateAliceConditioning n i (disjointCoordinateVector n ω))
      (X' := coordinateXBit n i)
      (Y' := coordinateMessage n p)
      (Z' := coordinateAliceConditioning n i)
      (by
        simpa [Function.comp_def, ν] using
          (identDistrib_disjointCoordinateVector_uniform n).comp
            (Measurable.of_discrete
            (f := fun coords =>
              (coordinateXBit n i coords, coordinateMessage n p coords,
                coordinateAliceConditioning n i coords))))
  -- Step 5: chain the two identities through the common `ν`-information.
  calc
    I[specialX n : message n p | aliceDynamicConditioning n ;
        (disjointCondMeasure n)[|specialCoordinate n ← i]]
        = I[specialX n : message n p | aliceDynamicConditioning n ; μi] := by
          rfl
    _ = I[coordinateXBit n i : coordinateMessage n p | coordinateAliceConditioning n i ; ν] :=
          hleft_congr.trans hleft_pull
    _ = fixedAliceInfoTerm n p i := (hright_congr.trans hright_pull).symm

open Classical in
/-- Alice's corrected information term is the average over `i` of the fixed-coordinate
summands: `I(X_T : M | T, X_<T, Y_≥T, D) = (1/n) Σ_i I(X_i : M | X_<i, Y_≥i, D)`
[RY20, Ch. 6, eq. (6.3)] (averaging Lemma 6.15 over uniform `T`). This holds because,
conditioned on `D`, `T` is uniform and independent of `(X, Y, M)`. -/
theorem aliceInfoTerm_eq_average_fixedAliceInfoTerm
    (p : ProtocolType n) :
    aliceInfoTerm n p =
      (∑ i : Fin n, fixedAliceInfoTerm n p i) / (n : ℝ) := by
  rw [aliceInfoTerm_eq_sum_specialCoordinate_fiber_info]
  simp_rw [aliceDynamicConditioning_fiber_info_eq_fixedAliceInfoTerm]
  rw [← Finset.mul_sum]
  ring

open Classical in
/-- Alice's corrected information term is at most the full-vector information divided by `n`:
`I(X_T : M | T, X_<T, Y_≥T, D) ≤ I(X : M | Y, D) / n` [RY20, Ch. 6, eq. (6.3)] (averaging
Lemma 6.15 over uniform `T`). This combines the averaging identity with the chain-rule
inequality `sum_fixedAliceInfoTerm_le_xVector_info`. -/
theorem aliceInfoTerm_le_average_xVector_info
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤
      I[xVector n : message n p | yVector n ; disjointCondMeasure n] / (n : ℝ) := by
  rw [aliceInfoTerm_eq_average_fixedAliceInfoTerm]
  exact div_le_div_of_nonneg_right (sum_fixedAliceInfoTerm_le_xVector_info n p) (by positivity)

open Classical in
/-- Bob's corrected information term is at most the full-vector information divided by `n`:
`I(Y_T : M | T, X_≤T, Y_>T, D) ≤ I(Y : M | X, D) / n` [RY20, Ch. 6, eq. (6.3)] (averaging
Lemma 6.15 over uniform `T`, second bound). Obtained from the Alice bound for the dual
protocol via the two duality identities. -/
theorem bobInfoTerm_le_average_yVector_info
    (p : ProtocolType n) :
    bobInfoTerm n p ≤
      I[yVector n : message n p | xVector n ; disjointCondMeasure n] / (n : ℝ) := by
  have h := aliceInfoTerm_le_average_xVector_info n (dualProtocol n p)
  simpa [aliceInfoTerm_dualProtocol_eq_bobInfoTerm,
    xVector_message_info_dualProtocol_eq_yVector_message_info] using h

open Classical in
/-- The full-vector information `I(X : M | Y, D)` between Alice's input and the transcript is
at most `ℓ · log 2`, where `ℓ` is the communication of the protocol: conditional mutual
information is at most the entropy of the transcript, which is at most `ℓ` bits
[RY20, Ch. 6, eq. (6.3)] (`ℓ/n ≥ I(A_T : S | Q B_T 𝒟)`, the numerator `ℓ`). Deviation:
natural-log units, so the bound reads `ℓ · log 2` rather than `ℓ`. -/
theorem xVector_message_info_le_complexity_mul_log_two
    (p : ProtocolType n) :
    I[xVector n : message n p | yVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := xVector n) (Y := message n p) (Z := yVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- The full-vector information `I(Y : M | X, D)` between Bob's input and the transcript is
at most `ℓ · log 2`, where `ℓ` is the communication of the protocol; the Bob mirror of
`xVector_message_info_le_complexity_mul_log_two` [RY20, Ch. 6, eq. (6.3)]. Deviation:
natural-log units, so the bound reads `ℓ · log 2` rather than `ℓ`. -/
theorem yVector_message_info_le_complexity_mul_log_two
    (p : ProtocolType n) :
    I[yVector n : message n p | xVector n ; disjointCondMeasure n] ≤
      p.complexity * Real.log 2 := by
  exact
    (ProbabilityTheory.condMutualInfo_le_entropy_right
      (μ := disjointCondMeasure n)
      (X := yVector n) (Y := message n p) (Z := xVector n)
      Measurable.of_discrete Measurable.of_discrete Measurable.of_discrete).trans
      (entropy_message_le_complexity_mul_log_two_of_measure n p (disjointCondMeasure n))

open Classical in
/-- Alice's corrected information term is at most `ℓ · log 2 / n` for a protocol of
communication `ℓ`: `I(X_T : M | T, X_<T, Y_≥T, D) ≤ ℓ · log 2 / n`
[RY20, Ch. 6, eq. (6.3)] (`ℓ/n ≥ I(A_T : S | Q B_T 𝒟)`). Deviation: natural-log units, so
the bound reads `ℓ · log 2 / n`. This chains the averaged chain-rule bound with the entropy
bound `H(M) ≤ ℓ · log 2`. -/
theorem aliceInfoTerm_le_average_entropy_bound
    (p : ProtocolType n) :
    aliceInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := aliceInfoTerm_le_average_xVector_info n p
  have hentropy := xVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

open Classical in
/-- Bob's corrected information term is at most `ℓ · log 2 / n` for a protocol of
communication `ℓ`: `I(Y_T : M | T, X_≤T, Y_>T, D) ≤ ℓ · log 2 / n`; the Bob mirror of
[RY20, Ch. 6, eq. (6.3)] (`ℓ/n ≥ I(A_T : S | Q B_T 𝒟)`). Deviation: natural-log units, so
the bound reads `ℓ · log 2 / n`. -/
theorem bobInfoTerm_le_average_entropy_bound
    (p : ProtocolType n) :
    bobInfoTerm n p ≤ (p.complexity * Real.log 2) / (n : ℝ) := by
  have hchain := bobInfoTerm_le_average_yVector_info n p
  have hentropy := yVector_message_info_le_complexity_mul_log_two n p
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  exact hchain.trans (div_le_div_of_nonneg_right hentropy hn_nonneg)

/-- The total corrected information `claimInfo` of a protocol of communication `ℓ` is at
most `2 ℓ · log 2 / n`: the sum of the Alice and Bob bounds `ℓ · log 2 / n`
[RY20, Ch. 6, eq. (6.3)] (`ℓ/n ≥ I(A_T : S | Q B_T 𝒟)`, applied on both sides). Deviation:
natural-log units, so the bound reads `ℓ · log 2 / n` per side. This is the upper half of
the headline argument; the lower half (`claimInfo` is bounded below by a constant for any
low-error protocol) is in `Headline.lean`.

**Proof sketch.** Unfold `claimInfo` as the sum of the two terms, bound each by
`ℓ · log 2 / n` (`aliceInfoTerm_le_average_entropy_bound`,
`bobInfoTerm_le_average_entropy_bound`), and add. -/
theorem claimInfo_le_average_info_upper
    (p : ProtocolType n) :
    claimInfo n p ≤ 2 * (p.complexity * Real.log 2) / (n : ℝ) := by
  rw [claimInfo]
  calc
    aliceInfoTerm n p + bobInfoTerm n p
        ≤ (p.complexity * Real.log 2) / (n : ℝ) +
            (p.complexity * Real.log 2) / (n : ℝ) :=
          add_le_add (aliceInfoTerm_le_average_entropy_bound n p)
            (bobInfoTerm_le_average_entropy_bound n p)
    _ = 2 * (p.complexity * Real.log 2) / (n : ℝ) := by ring

end RandomizedLowerBound

end Functions.Disjointness

end CommunicationComplexity
