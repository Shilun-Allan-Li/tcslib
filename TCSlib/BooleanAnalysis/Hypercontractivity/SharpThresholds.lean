import TCSlib.BooleanAnalysis.Hypercontractivity.SharpThresholdDefs
import TCSlib.BooleanAnalysis.Hypercontractivity.RandomizationDefs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sharp thresholds and structural theorems: statement skeletons

## Main definitions

Boosters, pseudo-juntas, and graph properties are defined in `SharpThresholdDefs`;
notable-coordinate families are in `RandomizationDefs`.

## Main results

* `friedgut_kalai_sharp_threshold`: Theorem 10.29.
* `friedgut_graph_sharp_threshold`: Friedgut's graph-property theorem.
* `bourgain_sharp_threshold`, `hatami_pseudo_junta`: the named theorems of §10.5.
* `bourgain_notable_coordinates`, `nonnotable_randomized_laplacian`: 10.47–10.48.

All constants are uniform over the product space and dimension. Heterogeneous products
extend the source's homogeneous presentation by the same coordinatewise argument.
Friedgut's conjecture is not asserted as a theorem. All proof bodies remain `sorry`.

## References

* [OD14] Ryan O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014;
  May 2021 arXiv edition, Theorem 10.29, §10.5, Theorem 10.47, Lemma 10.48 and Ex. 10.39.
-/

open scoped BigOperators Classical

namespace BooleanAnalysis.Hypercontractivity

universe u

/-- An increasing nonconstant transitive-symmetric Boolean function has the specified
narrow threshold window about a critical probability at most one half, with absolute
constant `B`. [OD14, Thm. 10.29] The assumption `2≤n` resolves the source formula's
undefined `log n` denominator at dimension one; true denotes the book's output `-1`.

**Proof sketch.** Apply biased KKL and Margulis–Russo throughout the proposed window.
Compare `p log(1/p)` with its critical value, then integrate the differential inequalities
for the threshold curve and its complement on the two sides of criticality. -/
theorem friedgut_kalai_sharp_threshold :
    ∃ B : ℝ, 0 < B ∧ ∀ (n : ℕ) (f : BoolCube n → Bool) (pc ε : ℝ),
      2 ≤ n → IsIncreasing f → IsTransitiveSymmetric f → (∃ x y, f x ≠ f y) →
      0 < pc → pc ≤ 1 / 2 → thresholdCurve f pc = 1 / 2 → 0 < ε → ε < 1 / 4 →
      let η := B * Real.log (1 / ε) * Real.log (1 / pc) / Real.log n
      η ≤ 1 / 2 → thresholdCurve f (pc * (1 - η)) ≤ ε ∧
        1 - ε ≤ thresholdCurve f (pc * (1 + η)) := sorry

/-- Increasing graph properties of bounded biased influence can be approximated by
monotone DNFs of width depending only on the influence bound and approximation error.
[OD14, §10.5, Friedgut's Sharp Threshold Theorem] Natural-valued width rounds up the
source's real bound; vertex count, edge count, and bias are uniformly quantified.

**Proof sketch.** Friedgut's structural argument extracts bounded-size positive witnesses
from bounded influence; their disjunction approximates the property. This is the deep
graph-property step cited in the textbook to Friedgut (1999). -/
theorem friedgut_graph_sharp_threshold :
    ∃ w : ℝ → ℝ → ℕ, ∀ (v n : ℕ) (edge : Fin n ≃ GraphEdge v)
      (f : BoolCube n → Bool) (p K ε : ℝ),
      0 < p → p ≤ 1 / 2 → 0 < K → 0 < ε → ε < 1 → IsIncreasing f →
      IsGraphProperty edge f → biasedTotalInfluence p f ≤ K →
      ∃ d : DNF n, IsMonotoneDNF d ∧ d.width ≤ w K ε ∧
        biasedProbability p (fun x => f x ≠ d.eval x) ≤ ε := sorry

/-- A Boolean function of influence at most `K` and variance at least `0.01` has, with
appreciable probability, a restriction to `O(K)` coordinates boosting its mean in one
fixed signed direction by at least `exp(-O(K²))`.
[OD14, §10.5, Bourgain's Sharp Threshold Theorem]

**Proof sketch.** Use Theorem 10.47 at a small fixed error. Positive variance forces
nonempty retained components to carry mass, so some component is large on many inputs.
Inclusion-exclusion gives a small booster; choose the more frequent direction. -/
theorem bourgain_sharp_threshold : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (K : ℝ),
      P.IsBoolean f → P.totalInfluence f ≤ K → (1 / 100 : ℝ) ≤ P.variance f →
      ∃ τ : ℝ, Real.exp (-C * K ^ 2) ≤ |τ| ∧
        |τ| ≤ P.prob (fun x => ∃ T : Finset (Fin n),
          (T.card : ℝ) ≤ D * K ∧ IsBooster P f T x τ) := sorry

/-- Every Boolean function of influence at most `K` is `ε`-close to a pseudo-junta
of expected width at most `exp(C K³/ε³)`, for an absolute `C`.
[OD14, §10.5, Hatami's Theorem]

**Proof sketch.** Retain significant low-degree components and expose their domains
through local tests. Hatami's structural argument bounds the expected exposed size.
Round the approximation to a Boolean function of the exposed observations. -/
theorem hatami_pseudo_junta : ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (K ε : ℝ),
      P.IsBoolean f → 0 ≤ K → P.totalInfluence f ≤ K → 0 < ε →
      ∃ h : P.Point → ℝ, P.IsBoolean h ∧
        IsPseudoJunta P h (Real.exp (C * K ^ 3 / ε ^ 3)) ∧
        P.prob (fun x => f x ≠ h x) ≤ ε := sorry

/-- A Boolean `K`-pseudo-junta has total influence at most `4K`.
[OD14, §10.5, discussion after Hatami's Theorem; Ex. 10.39]

**Proof sketch.** A resampled coordinate can change the output only if it is exposed
before or after resampling. Sum this probability bound over coordinates and use the
expected exposure-size bound. -/
theorem pseudo_junta_totalInfluence_le {n : ℕ} (P : FiniteProduct.{u} n)
    (h : P.Point → ℝ) (K : ℝ) (hh : P.IsBoolean h) (hJ : IsPseudoJunta P h K) :
    P.totalInfluence h ≤ 4 * K := sorry

/-- A Boolean function admits input-dependent coordinate sets of size `exp(O(k))`
retaining all but `2ε` expected squared-component mass, for `k=I[f]/ε`. Each retained
family has size `exp(O(k²))`. [OD14, Thm. 10.47]

**Proof sketch.** Discard degrees above `k` using the influence tail bound. Define notable
coordinates by pointwise spectral influence and use randomized hypercontractivity to
bound omitted mass. Truncate unusually large sets using Markov and fourth moments;
count their subsets of size at most `k`. -/
theorem bourgain_notable_coordinates : ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
    ∀ (n : ℕ) (P : FiniteProduct.{u} n) (f : P.Point → ℝ) (ε : ℝ),
      P.IsBoolean f → 0 < ε → ε < 1 / 2 →
      let k := P.totalInfluence f / ε
      ∃ J : P.Point → Finset (Fin n),
        (∀ x, ((J x).card : ℝ) ≤ Real.exp (C * k)) ∧
        (∀ x, ((notableFamily (J x) k).card : ℝ) ≤ Real.exp (D * k ^ 2)) ∧
        P.expect (fun x => ∑ S : Finset (Fin n),
          if S ∈ notableFamily (J x) k then 0 else P.component S f x ^ 2) ≤ 2 * ε := sorry

/-- At an input where a coordinate is not notable, the noisy randomized Laplacian has
squared second norm at most `τ^(1/3)` times its `(4/3)`-moment.
[OD14, Lem. 10.48] This real-valued version requires no Boolean range hypothesis.

**Proof sketch.** Apply cube `(4/3,2)`-hypercontractivity. Split the resulting squared norm
into powers `2/3` and `4/3`, bound the former using the second norm, and apply Parseval
and the non-notability hypothesis. -/
theorem nonnotable_randomized_laplacian {n : ℕ} (P : FiniteProduct.{u} n)
    (f : P.Point → ℝ) (x : P.Point) (i : Fin n) (τ : ℝ)
    (hτ : 0 < τ) (hi : i ∉ notableCoordinates P f τ x) :
    let g := P.noise (2 / 5) (P.laplacian i f)
    let gr := fun r => randomization P g r x
    cubeLpNorm 2 (noiseOp (1 / Real.sqrt 3) gr) ^ 2 ≤
      τ ^ (1 / 3 : ℝ) * cubeLpNorm (4 / 3) gr ^ (4 / 3 : ℝ) := sorry

end BooleanAnalysis.Hypercontractivity
