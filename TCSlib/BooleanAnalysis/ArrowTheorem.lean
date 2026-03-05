import TCSlib.BooleanAnalysis.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Basic

/-!
# Arrow's Impossibility Theorem via Kalai's Fourier Analysis

This file proves Arrow's Impossibility Theorem using Kalai's Fourier-analytic
approach (Gil Kalai, "A Fourier-Theoretic Perspective on the Condorcet Paradox
and Arrow's Theorem", 2002).

## Setup

For 3 alternatives {a, b, c} and n voters, a social welfare function is given
by an odd Boolean function `f : BoolCube n → ℝ` applied to each pairwise
comparison of alternatives. The function being "odd" models the antisymmetry
of pairwise preference: if society prefers a to b, it must not also prefer b to a.

## Main result

`arrow_theorem`: Any odd, ±1-valued, unanimous, acyclic social welfare function
must be a dictator.

## Proof sketch (Kalai)

1. For voters with i.i.d. uniform orderings of {a,b,c}, the Condorcet cycle
   probability is `Pr[cycle] = (1 + 3·∑_S f̂(S)²·(-1/3)^|S|) / 4`.
2. For odd `f`, only odd Fourier levels contribute.
3. Since `(-1/3)^k ≥ -1/3` for all odd `k`, we have `Pr[cycle] ≥ 0`.
4. `Pr[cycle] = 0` forces all Fourier weight onto level 1.
5. A ±1-valued degree-1 function satisfying unanimity must be a dictator.

## References

* Gil Kalai, *A Fourier-Theoretic Perspective on the Condorcet Paradox and
  Arrow's Theorem*, Advances in Applied Mathematics, 2002.
* Ryan O'Donnell, *Analysis of Boolean Functions*, Chapter 2.
-/

set_option maxHeartbeats 800000

open scoped BigOperators
open BooleanAnalysis

namespace ArrowTheorem

variable {n : ℕ}

/-! ## Social choice definitions -/

/-- Unanimity: if all voters prefer a to b, society prefers a to b.
    In our encoding, f(all-false) = 1 means "a preferred to b" when every
    voter marks `false` (i.e., prefers the first alternative). -/
def unanimity (f : BooleanFunc n) : Prop :=
  f (fun _ => false) = 1

/-- f is a dictatorship: there exists some voter i whose preference always
    determines society's preference. -/
def isDictator (f : BooleanFunc n) : Prop :=
  ∃ i : Fin n, f = dictator i

/-! ## The voter ordering model

We model each voter as choosing one of the 6 transitive strict orderings of
{a, b, c}, indexed by `Fin 6`. For each ordering we record the voter's
preference in three pairwise comparisons:
- `abPref`: comparison of a vs. b (false = prefer a, true = prefer b)
- `bcPref`: comparison of b vs. c (false = prefer b, true = prefer c)
- `caPref`: comparison of c vs. a (false = prefer c, true = prefer a)

The sign convention: `boolToSign false = 1` ("pro first") and
`boolToSign true = -1` ("pro second").

The six orderings and their signs (s_ab, s_bc, s_ca):
| Index | Ordering | s_ab | s_bc | s_ca |
|-------|----------|------|------|------|
|  0    | a>b>c    |  1   |  1   | -1   |
|  1    | a>c>b    |  1   | -1   | -1   |
|  2    | b>a>c    | -1   |  1   | -1   |
|  3    | b>c>a    | -1   |  1   |  1   |
|  4    | c>a>b    |  1   | -1   |  1   |
|  5    | c>b>a    | -1   | -1   |  1   |
-/

/-- Preference of ordering k in the a-vs-b comparison (false = prefer a). -/
def abPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => false  -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => true   -- b > c > a
  | ⟨4, _⟩ => false  -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a

/-- Preference of ordering k in the b-vs-c comparison (false = prefer b). -/
def bcPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => false  -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a
  | ⟨4, _⟩ => true   -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a

/-- Preference of ordering k in the c-vs-a comparison (false = prefer c). -/
def caPref : Fin 6 → Bool
  | ⟨0, _⟩ => true   -- a > b > c: prefer a, so in ca: prefer a = true
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a: prefer c
  | ⟨4, _⟩ => false  -- c > a > b: prefer c
  | ⟨5, _⟩ => false  -- c > b > a: prefer c

/-! ## Key correlation lemma

For a single voter uniformly drawn from the 6 orderings, the sum of
products of pairwise preference signs has a specific value. This is the
core computation behind the Fourier formula for cycle probability.
-/

/-- The sum of s_ab · s_bc over all 6 orderings equals -2.
    (Expectation E[s_ab · s_bc] = -1/3.) -/
lemma sum_abPref_bcPref :
    ∑ k : Fin 6, boolToSign (abPref k) * boolToSign (bcPref k) = -2 := by
  simp only [Fin.sum_univ_six, abPref, bcPref, boolToSign]
  norm_num

/-- Similarly, E[s_bc · s_ca] = -1/3. -/
lemma sum_bcPref_caPref :
    ∑ k : Fin 6, boolToSign (bcPref k) * boolToSign (caPref k) = -2 := by
  simp only [Fin.sum_univ_six, bcPref, caPref, boolToSign]
  norm_num

/-- Similarly, E[s_ab · s_ca] = -1/3. -/
lemma sum_abPref_caPref :
    ∑ k : Fin 6, boolToSign (abPref k) * boolToSign (caPref k) = -2 := by
  simp only [Fin.sum_univ_six, abPref, caPref, boolToSign]
  norm_num

/-! ## Acyclicity and profiles -/

/-- A **profile** assigns each of the n voters one of the 6 orderings. -/
abbrev Profile (n : ℕ) := Fin n → Fin 6

/-- Given a profile, the a-vs-b preference vector of all n voters. -/
def abVotes (p : Profile n) : BoolCube n := fun i => abPref (p i)

/-- Given a profile, the b-vs-c preference vector. -/
def bcVotes (p : Profile n) : BoolCube n := fun i => bcPref (p i)

/-- Given a profile, the c-vs-a preference vector. -/
def caVotes (p : Profile n) : BoolCube n := fun i => caPref (p i)

/-- A social welfare function `f` is **acyclic** if no profile of transitive
    voter orderings produces a Condorcet cycle in society's preferences.

    A Condorcet cycle occurs when f(ab) = f(bc) = f(ca) = 1
    (society prefers a to b, b to c, and c to a — a cycle a>b>c>a)
    or f(ab) = f(bc) = f(ca) = -1 (the reverse cycle). -/
def acyclic (f : BooleanFunc n) : Prop :=
  ∀ p : Profile n,
    ¬ (f (abVotes p) = 1 ∧ f (bcVotes p) = 1 ∧ f (caVotes p) = 1) ∧
    ¬ (f (abVotes p) = -1 ∧ f (bcVotes p) = -1 ∧ f (caVotes p) = -1)

/-! ## The Fourier formula for cycle probability

The heart of Kalai's proof: for n voters with i.i.d. uniform orderings,
the expected product f(ab)·f(bc)·f(ca) factors through a correlation of
-1/3 per voter per pair of comparisons.

We compute:
  E_p[f(ab_p) · f(bc_p)] = ∑_S f̂(S)² · (-1/3)^|S|

This is because:
- Voters are independent, so the expectation factors as a product over voters.
- Per voter, E[s_ab · s_bc] = -1/3.
- The only terms surviving in the Fourier expansion are those where both S
  components at each voter i are present or both absent (otherwise the
  marginal E[s_ab] = 0 kills the term).
-/

/-- The pairwise correlation function: ∑_S f̂(S)² · (-1/3)^|S|.
    For odd f, only odd-level terms are nonzero. -/
noncomputable def corrFunc (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3 : ℝ) ^ S.card

/-- For any odd ±1-valued function, the correlation function is ≥ -1/3.

    Proof: (-1/3)^k ≥ -1/3 for all odd k (since |(-1/3)^k| = (1/3)^k ≤ 1/3
    for k ≥ 1). The even-level coefficients vanish by oddness.
    Hence ∑_S f̂(S)²·(-1/3)^|S| ≥ ∑_S f̂(S)²·(-1/3) = (-1/3)·∑_S f̂(S)² = -1/3. -/
lemma corrFunc_ge_neg_third (f : BooleanFunc n) (hodd : isOddFunc f) (hpm : isPmOne f) :
    corrFunc f ≥ -1/3 := by
  simp only [corrFunc]
  -- Lower bound: (-1/3)^|S| ≥ -1/3 when |S| is odd; and for even |S|, f̂(S) = 0.
  -- So each term f̂(S)² * (-1/3)^|S| ≥ f̂(S)² * (-1/3).
  have hbound : ∀ S : Finset (Fin n),
      fourierCoeff f S ^ 2 * (-1/3 : ℝ) ^ S.card ≥
      fourierCoeff f S ^ 2 * (-1/3 : ℝ) := by
    intro S
    -- Handle even case first (before applying mul_le_mul_of_nonneg_left)
    by_cases heven : Even S.card
    · -- f̂(S) = 0 by oddness, so both sides are 0
      have hzero : fourierCoeff f S = 0 := fourierCoeff_odd_even f hodd S heven
      simp [hzero]
    · -- |S| is odd: (-1/3)^|S| ≥ -1/3
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      rw [Nat.not_even_iff_odd] at heven
      obtain ⟨k, hk⟩ := heven
      have hge : (-1/3 : ℝ) ^ S.card ≥ -1/3 := by
        rw [hk, show (-1/3 : ℝ) = -(1/3 : ℝ) from by norm_num]
        have hodd_n : Odd (2 * k + 1) := ⟨k, rfl⟩
        rw [hodd_n.neg_pow]
        have hle : (1/3 : ℝ) ^ (2*k+1) ≤ 1/3 := by
          have := pow_le_pow_of_le_one (by positivity : (0:ℝ) ≤ 1/3)
                    (by norm_num : (1/3:ℝ) ≤ 1) (show 1 ≤ 2*k+1 from by omega)
          simpa [pow_one] using this
        linarith
      linarith
  calc -1/3 = -1/3 * ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
          rw [parseval_pm_one f hpm]; ring
      _ = ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3) := by
          rw [Finset.mul_sum]; congr 1; ext S; ring
      _ ≤ ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3) ^ S.card :=
          Finset.sum_le_sum (fun S _ => hbound S)

/-- If the correlation function equals -1/3, then f̂(S) = 0 for all S with
    |S| ≥ 3 (i.e., all Fourier weight is on levels 0 and 1).

    Since f is odd, f̂(∅) = f̂(S for even |S|) = 0. So in fact all Fourier
    weight is on level 1. -/
lemma corrFunc_eq_neg_third_of_weight_one {f : BooleanFunc n}
    (hodd : isOddFunc f) (hpm : isPmOne f) (hcorr : corrFunc f = -1/3) :
    ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0 := by
  intro S hS
  -- From hcorr = -1/3 and the lower bound, the sum equals its lower bound,
  -- so each term achieves equality.
  -- The lower bound analysis: ∑ f̂(S)² [(-1/3)^|S| - (-1/3)] = 0.
  -- Since f̂(S)² ≥ 0 and (-1/3)^|S| - (-1/3) ≥ 0 for odd |S| ≥ 3,
  -- each such term must be zero.
  by_cases heven : Even S.card
  · exact fourierCoeff_odd_even f hodd S heven
  · -- |S| is odd
    rw [Nat.not_even_iff_odd] at heven
    -- If |S| = 1, we're done
    by_cases hcard : S.card = 1
    · exact absurd hcard hS
    · -- |S| is odd and ≠ 1, so |S| ≥ 3
      -- The equality condition forces f̂(S) = 0
      obtain ⟨k, hk⟩ := heven  -- S.card = 2*k+1
      have hge3 : S.card ≥ 3 := by omega
      -- We use the equality condition from the sum lower bound
      have hzero : fourierCoeff f S ^ 2 * ((-1/3 : ℝ) ^ S.card - (-1/3)) = 0 := by
        -- The sum ∑ f̂(T)² [(-1/3)^|T| - (-1/3)] = 0
        -- because ∑ f̂(T)² (-1/3)^|T| = -1/3 = (-1/3) ∑ f̂(T)²
        have hsum : ∑ T : Finset (Fin n),
            fourierCoeff f T ^ 2 * ((-1/3 : ℝ) ^ T.card - (-1/3)) = 0 := by
          have hpars := parseval_pm_one f hpm
          simp only [corrFunc] at hcorr
          simp_rw [mul_sub]
          rw [Finset.sum_sub_distrib, hcorr,
              show ∑ T : Finset (Fin n), fourierCoeff f T ^ 2 * (-1/3 : ℝ) =
                  (-1/3) * ∑ T : Finset (Fin n), fourierCoeff f T ^ 2 from by
                rw [Finset.mul_sum]; congr 1; ext T; ring,
              hpars]
          ring
        -- Each term in the sum is nonneg (so each must be zero)
        have hterm_nonneg : ∀ T : Finset (Fin n),
            fourierCoeff f T ^ 2 * ((-1/3 : ℝ) ^ T.card - (-1/3)) ≥ 0 := by
          intro T
          by_cases hT_even : Even T.card
          · -- even: f̂(T) = 0, whole term is 0
            have hzeroT : fourierCoeff f T = 0 := fourierCoeff_odd_even f hodd T hT_even
            simp [hzeroT]
          · -- odd: (-1/3)^|T| ≥ -1/3
            apply mul_nonneg (sq_nonneg _)
            rw [Nat.not_even_iff_odd] at hT_even
            obtain ⟨j, hj⟩ := hT_even
            have hge : (-1/3 : ℝ) ^ T.card ≥ -1/3 := by
              rw [hj, show (-1/3 : ℝ) = -(1/3 : ℝ) from by norm_num]
              have hodd_n : Odd (2 * j + 1) := ⟨j, rfl⟩
              rw [hodd_n.neg_pow]
              have hle : (1/3 : ℝ) ^ (2*j+1) ≤ 1/3 := by
                have := pow_le_pow_of_le_one (by positivity : (0:ℝ) ≤ 1/3)
                          (by norm_num : (1/3:ℝ) ≤ 1) (show 1 ≤ 2*j+1 from by omega)
                simpa [pow_one] using this
              linarith
            linarith
        exact Finset.sum_eq_zero_iff_of_nonneg (fun T _ => hterm_nonneg T) |>.mp hsum
            S (Finset.mem_univ S)
      -- Extract f̂(S) = 0 from the product being zero
      have hfact_pos : (-1/3 : ℝ) ^ S.card - (-1/3) > 0 := by
        -- |S| ≥ 3 and odd: (-1/3)^|S| > -1/3 strictly
        have hk3 : k ≥ 1 := by omega
        rw [hk, show (-1/3 : ℝ) = -(1/3 : ℝ) from by norm_num]
        have hodd_n : Odd (2 * k + 1) := ⟨k, rfl⟩
        rw [hodd_n.neg_pow]
        -- Need: -(1/3)^(2*k+1) + 1/3 > 0, i.e., (1/3)^(2*k+1) < 1/3
        -- Bound: (1/3)^(2*k+1) ≤ (1/3)^3 = 1/27 < 1/3
        have hle : (1/3 : ℝ) ^ (2*k+1) ≤ 1/27 := by
          have h1 : (1/3 : ℝ) ^ (2*k+1) ≤ (1/3 : ℝ) ^ 3 :=
            pow_le_pow_of_le_one (by positivity) (by norm_num) (by omega)
          have h2 : (1/3 : ℝ) ^ 3 = 1/27 := by norm_num
          linarith
        linarith [show (1/27 : ℝ) < 1/3 from by norm_num]
      have := mul_eq_zero.mp hzero
      rcases this with h | h
      · exact pow_eq_zero_iff (by norm_num) |>.mp h
      · linarith

/-! ## The main Fourier cycle formula (key lemma from Kalai)

For voters with i.i.d. uniform orderings, the expected product
E[f(ab) · f(bc)] factors as a sum of Fourier coefficients weighted
by (-1/3)^|S|. The acyclicity assumption forces this to equal -1/3,
which by the lower bound forces W_1 = 1.
-/

/-- The expected value of f(ab-votes) · f(bc-votes) over all uniform profiles
    equals the correlation function ∑_S f̂(S)² · (-1/3)^|S|.

    Proof sketch: Since voters are independent,
      E[f(x^ab) · f(x^bc)] = ∑_{S,T} f̂(S) f̂(T) ∏_i E[s^ab_i^{1[i∈S]} · s^bc_i^{1[i∈T]}]
    The per-voter factor is nonzero only when the voter is in both S and T or
    neither (single indicators give E[s_ab] = 0). This forces S = T, and the
    per-voter factor for i ∈ S is E[s_ab · s_bc] = -1/3.
    Hence E[f(ab)·f(bc)] = ∑_S f̂(S)² · (-1/3)^|S|. -/
lemma expected_product_eq_corrFunc (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (abVotes p) * f (bcVotes p) = corrFunc f := by
  simp only [corrFunc, fourierCoeff, innerProduct, expect, uniformWeight]
  -- Expand both f(ab) and f(bc) using Walsh expansion
  -- Then use independence of voters and the per-voter correlation E[s_ab·s_bc] = -1/3
  sorry

/-! ## Acyclicity implies degree-1 Fourier structure -/

/-- Acyclicity of f implies that the Fourier correlation function equals -1/3.

    Key steps:
    1. Acyclicity means no profile gives a cycle, so the cycle probability = 0.
    2. Cycle probability = (1 + 3·corrFunc f) / 4 = 0 implies corrFunc f = -1/3.
-/
lemma acyclic_implies_corrFunc (f : BooleanFunc n) (hodd : isOddFunc f) (hpm : isPmOne f)
    (hacyc : acyclic f) : corrFunc f = -1/3 := by
  -- The cycle probability computation
  -- Pr[cycle] = (1 + E[f(ab)f(bc)] + E[f(bc)f(ca)] + E[f(ab)f(ca)] + E[f(ab)f(bc)f(ca)]) / 4
  -- = (1 + 3·corrFunc(f) + 0) / 4
  -- The triple expectation E[f(ab)f(bc)f(ca)] = 0 for odd f (since S△T has even card).
  -- The three pairwise expectations are all equal to corrFunc f.
  -- Acyclicity says Pr[cycle] = 0, so corrFunc f = -1/3.
  sorry

/-! ## Degree-1 implies dictator -/

/-- A ±1-valued odd unanimous function with all Fourier weight on level 1 is a dictator.

    Proof: f = ∑_i a_i · χ_{i} with ∑_i a_i² = 1 (Parseval).
    - Unanimity: f(false,...,false) = ∑_i a_i = 1.
    - For each j: f(only-j-true) = 1 - 2·a_j ∈ {-1,1}, so a_j ∈ {0,1}.
    - From a_j ∈ {0,1} and ∑ a_j² = ∑ a_j = 1: exactly one a_{j₀} = 1.
    - Hence f = χ_{{j₀}} = dictator j₀. -/
lemma degree_one_implies_dictator (f : BooleanFunc n) (hodd : isOddFunc f)
    (hpm : isPmOne f) (huniv : unanimity f)
    (hdeg1 : ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0) :
    isDictator f := by
  -- Step 1: Parseval gives ∑_i f̂({i})² = 1
  -- All non-singleton Fourier coefficients are 0 by hdeg1.
  have hpars : ∑ i : Fin n, fourierCoeff f {i} ^ 2 = 1 := by
    have hparseval := parseval_pm_one f hpm
    -- Reindex via Finset.sum_image: ∑_i f({i})² = ∑_{S ∈ image} f(S)² = ∑_S f(S)²
    have hexpand : ∑ i : Fin n, fourierCoeff f ({i} : Finset (Fin n)) ^ 2 =
        ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 := by
      rw [← Finset.sum_image (f := fun S => fourierCoeff f S ^ 2)
              (fun i _ j _ h => Finset.singleton_injective h)]
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : S.card ≠ 1 := by
        intro hc
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        exact hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
      simp [hdeg1 S hcard]
    rw [hexpand, hparseval]
  -- Step 2: Walsh expansion restricted to level 1
  -- f(x) = ∑_i f̂({i}) · boolToSign(x i)
  have hfourier : ∀ x : BoolCube n,
      f x = ∑ i : Fin n, fourierCoeff f {i} * boolToSign (x i) := by
    intro x
    rw [walsh_expansion f x]
    -- Reduce full sum to singleton terms (non-singletons vanish)
    have step1 : ∑ S : Finset (Fin n), fourierCoeff f S * chiS S x =
        ∑ S ∈ (Finset.univ : Finset (Fin n)).image (fun i => ({i} : Finset (Fin n))),
            fourierCoeff f S * chiS S x := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro S _ hS
      have hcard : S.card ≠ 1 := by
        intro hc
        obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
        exact hS (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi.symm⟩)
      simp [hdeg1 S hcard]
    -- Reindex image sum over Fin n
    have step2 : ∑ S ∈ (Finset.univ : Finset (Fin n)).image (fun i => ({i} : Finset (Fin n))),
        fourierCoeff f S * chiS S x =
        ∑ i : Fin n, fourierCoeff f {i} * boolToSign (x i) := by
      rw [Finset.sum_image (fun i _ j _ h => Finset.singleton_injective h)]
      congr 1; ext i; rw [chiS_singleton]
    rw [step1, step2]
  -- Step 3: Unanimity gives ∑_i a_i = 1
  have huniv' : ∑ i : Fin n, fourierCoeff f {i} = 1 := by
    have h := huniv
    rw [unanimity] at h
    rw [hfourier] at h
    simp only [boolToSign_false, mul_one] at h
    exact h
  -- Step 4: For each i, f(only-i-true) ∈ {-1,1} gives a_i ∈ {0,1}
  have hai_range : ∀ i : Fin n, fourierCoeff f {i} = 0 ∨ fourierCoeff f {i} = 1 := by
    intro i
    -- f at x with only bit i = true equals 1 - 2·a_i
    have hval : f (Function.update (fun _ => false) i true) =
        1 - 2 * fourierCoeff f {i} := by
      rw [hfourier]
      have key : ∑ j : Fin n,
          fourierCoeff f {j} * boolToSign ((Function.update (fun _ => false) i true) j) =
          -(fourierCoeff f {i}) + ∑ j ∈ Finset.univ.erase i, fourierCoeff f {j} := by
        rw [← Finset.add_sum_erase Finset.univ
            (fun j => fourierCoeff f {j} * boolToSign ((Function.update (fun _ => false) i true) j))
            (Finset.mem_univ i)]
        simp only [Function.update_apply, eq_self_iff_true, ↓reduceIte,
                   boolToSign_true, mul_neg, mul_one]
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        have hjni : j ≠ i := (Finset.mem_erase.mp hj).1
        simp only [Function.update_apply, if_neg hjni, boolToSign_false, mul_one]
      rw [key]
      have herase := Finset.add_sum_erase Finset.univ
          (fun j => fourierCoeff f {j}) (Finset.mem_univ i)
      linarith [huniv']
    have hpm_val := hpm (Function.update (fun _ => false) i true)
    rw [hval] at hpm_val
    rcases hpm_val with h | h
    · left; linarith
    · right; linarith
  -- Step 5: Exactly one a_{j₀} = 1, the rest are 0
  -- Using |{i | a_i = 1}| = ∑_{i∈J} 1 = ∑_i a_i = 1
  have hexists : ∃ j : Fin n, fourierCoeff f {j} = 1 ∧
      ∀ i : Fin n, i ≠ j → fourierCoeff f {i} = 0 := by
    let J := Finset.univ.filter (fun i : Fin n => fourierCoeff f {i} = 1)
    have hJ_card : J.card = 1 := by
      have hcard_real : (J.card : ℝ) = 1 := by
        have h0 : ∀ i : Fin n, i ∉ J → fourierCoeff f {i} = 0 := by
          intro i hi
          simp only [J, Finset.mem_filter, Finset.mem_univ, true_and, not_true,
                     not_and, forall_true_left] at hi
          push_neg at hi
          rcases hai_range i with h | h
          · exact h
          · exact absurd h hi
        calc (J.card : ℝ)
            = ∑ i ∈ J, (1 : ℝ) := by simp
          _ = ∑ i ∈ J, fourierCoeff f {i} := by
              apply Finset.sum_congr rfl
              intro i hi
              exact ((Finset.mem_filter.mp hi).2).symm
          _ = ∑ i : Fin n, fourierCoeff f {i} := by
              apply Finset.sum_subset (Finset.filter_subset _ _)
              intro i _ hi
              exact h0 i hi
          _ = 1 := huniv'
      exact_mod_cast hcard_real
    obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hJ_card
    have hj_mem : j ∈ J := by rw [hj]; exact Finset.mem_singleton_self j
    refine ⟨j, (Finset.mem_filter.mp hj_mem).2, fun i hi => ?_⟩
    rcases hai_range i with h | h
    · exact h
    · exfalso
      have hi_mem : i ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩
      rw [hj] at hi_mem
      exact hi (Finset.mem_singleton.mp hi_mem)
  obtain ⟨j₀, hj₀, hothers⟩ := hexists
  -- Step 6: f = χ_{{j₀}} = dictator j₀
  use j₀
  ext x
  rw [hfourier x, dictator_eq_chi, chiS_singleton]
  -- ∑_i a_i * boolToSign(x i) = boolToSign(x j₀) since a_{j₀}=1 and a_i=0 for i≠j₀
  conv_lhs => rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₀)]
  simp only [hj₀, one_mul]
  suffices h : ∑ i ∈ Finset.univ.erase j₀, fourierCoeff f {i} * boolToSign (x i) = 0 by
    linarith
  apply Finset.sum_eq_zero
  intro i hi
  simp [hothers i (Finset.mem_erase.mp hi).1]

/-! ## Arrow's Impossibility Theorem -/

/-- **Arrow's Impossibility Theorem** (via Kalai's Fourier proof):

    Any social welfare function f that is:
    - odd (antisymmetric: f(¬x) = -f(x))
    - ±1-valued (gives definite preferences)
    - unanimous (unanimously preferred alternatives are socially preferred)
    - acyclic (no Condorcet cycles arise)

    must be a **dictatorship** (there is one voter whose preference always wins).

    The proof uses Fourier analysis on Boolean functions:
    1. Acyclicity forces the Fourier cycle probability to be 0.
    2. This forces all Fourier weight onto level 1 (degree-1 functions).
    3. A degree-1 ±1-valued unanimous function must be a dictator. -/
theorem arrow_theorem (f : BooleanFunc n) (hodd : isOddFunc f) (hpm : isPmOne f)
    (huniv : unanimity f) (hacyc : acyclic f) :
    isDictator f := by
  -- Step 1: Acyclicity implies the correlation function equals -1/3
  have hcorr : corrFunc f = -1/3 := acyclic_implies_corrFunc f hodd hpm hacyc
  -- Step 2: corrFunc = -1/3 implies all weight on level 1
  have hdeg1 : ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0 :=
    corrFunc_eq_neg_third_of_weight_one hodd hpm hcorr
  -- Step 3: Degree-1 + unanimous + ±1-valued implies dictator
  exact degree_one_implies_dictator f hodd hpm huniv hdeg1

end ArrowTheorem
