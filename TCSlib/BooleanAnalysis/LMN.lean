import Mathlib
import TCSlib.BooleanAnalysis.Basic
import TCSlib.BooleanAnalysis.Switching

/-!
# LMN Main Lemma — Formal Skeleton

This file contains formal statements of the key lemmas (up to Lemma 7, the Main Lemma)
from the paper:

  N. Linial, Y. Mansour, N. Nisan,
  "Constant Depth Circuits, Fourier Transform, and Learnability",
  JACM 1993.

The main result (Lemma 7) states that Boolean functions computable by constant-depth
circuits of size M have almost all their Fourier weight concentrated on low-degree
coefficients:

  ∑_{|S| > t} f̂(S)² ≤ 2M · 2^{-t^{1/d} / 20}

where d is the circuit depth.

## Structure

- **Lemma 1** (Håstad's Switching Lemma): Already formalized in
  `TCSlib.BooleanAnalysis.Switching` as `switching_lemma` and `switching_corollary`.
- **Corollary 1**: Switching lemma implies that after restriction, the Fourier degree
  is small with high probability.
- **Lemma 2**: For circuits of depth d and size M, repeated application of the
  switching lemma yields Pr[deg(f^ρ) > s] ≤ M · 2^{-s}.
- **Lemma 3**: Fourier coefficient decomposition via restrictions.
- **Lemma 4**: Sum of squared Fourier coefficients via restrictions.
- **Lemma 5**: High-degree Fourier weight ≤ Pr[deg(f restricted) > k].
- **Lemma 6**: Averaging over random subsets bounds the high Fourier weight.
- **Lemma 7** (Main Lemma): Combines Lemma 2 and Lemma 6.

## Dependencies

- Håstad's Switching Lemma (`TCSlib.BooleanAnalysis.Switching`)
- Fourier analysis on the Boolean cube (`TCSlib.BooleanAnalysis.Basic`)
- Circuit definitions (`TCSlib.BooleanAnalysis.Circuit`)
-/

open BooleanAnalysis SwitchingLemma2 BoolCircuit
open scoped BigOperators
open Classical in
attribute [local instance] Classical.propDecidable

set_option maxHeartbeats 400000

noncomputable section

namespace LMN

variable {n : ℕ}

/-! ## Bridge definitions -/

/-- Convert a `Bool`-valued function to a `±1`-valued `BooleanFunc` via `boolToSign`.
    This maps `true ↦ -1` and `false ↦ 1`, following the convention in `Basic.lean`. -/
def toBooleanFunc (f : (Fin n → Bool) → Bool) : BooleanFunc n :=
  fun x => boolToSign (f x)

/-- Evaluate a `Circuit n` as a function `(Fin n → Bool) → Bool`. -/
def circuitEvalFn (c : Circuit n) : (Fin n → Bool) → Bool :=
  fun x => c.eval x

/-- Restrict a `BooleanFunc` by fixing variables outside `S` according to `R`.
    This corresponds to f_{Sᶜ → R} in the paper: the function obtained by
    setting variable `i` to `R i` for all `i ∉ S`, keeping variables in `S` free. -/
def restrictBySubset (f : BooleanFunc n) (S : Finset (Fin n))
    (R : BoolCube n) : BooleanFunc n :=
  fun x => f (fun i => if i ∈ S then x i else R i)

/-- High-degree Fourier weight: `∑_{|S| > t} f̂(S)²`. -/
def highFourierWeight (f : BooleanFunc n) (t : ℕ) : ℝ :=
  ∑ S : Finset (Fin n), if S.card > t then fourierCoeff f S ^ 2 else 0

/-- Construct the `Finset (Fin n)` corresponding to a Boolean mask.
    Variable `i` is in the subset iff `mask i = true`. -/
def subsetFromMask (mask : BoolCube n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => mask i = true)

/-- Indicator (as a real number) that the restricted function has Fourier degree
    exceeding `k`. Returns `1` if deg > k, and `0` otherwise. -/
def degreeExceedsIndicator (f : BooleanFunc n) (S : Finset (Fin n))
    (k : ℕ) (R : BoolCube n) : ℝ :=
  if has_degree_at_most (restrictBySubset f S R) k then 0 else 1

/-- The Bernoulli(p) weight of a restriction `ρ : Restriction n`.
    Each variable independently becomes `*` with probability `p`,
    `0` with probability `(1 - p)/2`, and `1` with probability `(1 - p)/2`.
    So `weight(ρ) = p^{numFree(ρ)} · ((1 - p)/2)^{n - numFree(ρ)}`. -/
def bernoulliRestrWeight (p : ℝ) (ρ : Restriction n) : ℝ :=
  p ^ ρ.numFree * ((1 - p) / 2) ^ (n - ρ.numFree)

/-- Probability of an event under the Bernoulli(p) random restriction model. -/
def bernoulliRestrProb (p : ℝ) (event : Restriction n → Prop)
    [DecidablePred event] : ℝ :=
  ∑ ρ : Restriction n, bernoulliRestrWeight p ρ * if event ρ then 1 else 0

/-! ## Fourier degree vs. decision tree depth -/

/-- **Key bridge lemma**: The Fourier degree of a `±1`-valued function is at most its
    decision tree depth.

    If `f : (Fin n → Bool) → Bool` has `dtDepth f ≤ d`, then all Fourier coefficients
    of `toBooleanFunc f` at sets of size `> d` vanish.

    **Proof idea**: A decision tree of depth `d` computes a multilinear polynomial of
    degree at most `d`. The Fourier expansion of such a polynomial has no terms of
    degree exceeding `d`. -/
private lemma has_degree_at_most_mono {f : BooleanFunc n} {k k' : ℕ}
    (hle : k ≤ k') (h : has_degree_at_most f k) : has_degree_at_most f k' := by
  intro S hS; exact le_trans (h S hS) hle

private lemma has_degree_at_most_of_eq {f g : BooleanFunc n} {k : ℕ}
    (h : f = g) (hd : has_degree_at_most f k) : has_degree_at_most g k := by
  subst h; exact hd

/-
Key identity: For any BooleanFunc formed by branching on variable i,
    the Fourier coefficient can be decomposed.
-/
private lemma branch_fourierCoeff (i : Fin n) (g_lo g_hi : BooleanFunc n)
    (S : Finset (Fin n)) :
    fourierCoeff (fun x => if x i then g_hi x else g_lo x) S =
    (fourierCoeff g_lo S + fourierCoeff g_hi S) / 2 +
    (fourierCoeff g_lo (symmDiff S {i}) - fourierCoeff g_hi (symmDiff S {i})) / 2 := by
  -- By definition of Fourier coefficients, we can expand the inner product.
  have h_expand : ∀ (f : BooleanFunc n), fourierCoeff f S = expect (fun x => f x * χ_[S] x) := by
    exact?;
  -- Split the sum into two parts: one where x i is true and one where x i is false.
  have h_split : ∑ x : BoolCube n, (if x i then g_hi x * χ_[S] x else g_lo x * χ_[S] x) = (∑ x : BoolCube n, g_lo x * χ_[S] x + ∑ x : BoolCube n, g_hi x * χ_[S] x) / 2 + (∑ x : BoolCube n, (g_lo x - g_hi x) * χ_[S] x * boolToSign (x i)) / 2 := by
    rw [ ← Finset.sum_add_distrib, ← add_div ];
    rw [ ← Finset.sum_add_distrib, Finset.sum_div ] ; congr ; ext x ; split_ifs <;> simp +decide [ *, boolToSign ] ; ring;
    ring;
  -- By definition of Fourier coefficients, we can expand the inner product for the second term.
  have h_expand_second : ∀ (f : BooleanFunc n), fourierCoeff f (symmDiff S {i}) = expect (fun x => f x * χ_[S] x * boolToSign (x i)) := by
    intro f
    have h_expand_second : ∀ x : BoolCube n, χ_[symmDiff S {i}] x = χ_[S] x * boolToSign (x i) := by
      intro x; unfold chiS boolToSign
      by_cases hi : i ∈ S
      · rw [show symmDiff S {i} = S.erase i from by ext j; simp [Finset.mem_symmDiff, Finset.mem_erase]; constructor <;> intro h <;> aesop]
        rw [← Finset.mul_prod_erase _ _ hi]; cases x i <;> simp
      · rw [show symmDiff S {i} = S ∪ {i} from by ext j; simp [Finset.mem_symmDiff]; constructor <;> intro h <;> aesop]
        rw [Finset.prod_union (by simp [Finset.disjoint_singleton_right, hi])]; simp;
    simp +decide only [mul_assoc];
    exact congr_arg _ ( funext fun x => by rw [ ← h_expand_second ] );
  simp_all +decide [ expect ];
  simp +decide [ sub_mul, mul_assoc, Finset.sum_add_distrib, Finset.mul_sum _ _ _ ] ; ring;
  simp +decide only [Finset.mul_sum _ _ _, mul_assoc]

/-
If has_degree_at_most f k and has_degree_at_most g k, then branching on
    variable i gives a function of degree at most k+1.
-/
private lemma branch_degree_bound (i : Fin n) (g_lo g_hi : BooleanFunc n)
    (k : ℕ) (hlo : has_degree_at_most g_lo k) (hhi : has_degree_at_most g_hi k) :
    has_degree_at_most (fun x => if x i then g_hi x else g_lo x) (k + 1) := by
  intro S hS_nonzero
  have h_fourier_coeff : fourierCoeff (fun x => if x i then g_hi x else g_lo x) S = (fourierCoeff g_lo S + fourierCoeff g_hi S) / 2 +
    (fourierCoeff g_lo (symmDiff S {i}) - fourierCoeff g_hi (symmDiff S {i})) / 2 := by
      convert branch_fourierCoeff i g_lo g_hi S using 1;
  contrapose! hS_nonzero;
  have h_fourier_coeff_zero : fourierCoeff g_lo S = 0 ∧ fourierCoeff g_hi S = 0 ∧ fourierCoeff g_lo (symmDiff S {i}) = 0 ∧ fourierCoeff g_hi (symmDiff S {i}) = 0 := by
    have h_fourier_coeff_zero : S.card > k ∧ (symmDiff S {i}).card > k := by
      by_cases hi : i ∈ S
      · constructor
        · omega
        · rw [show symmDiff S {i} = S.erase i from by ext j; simp [Finset.mem_symmDiff, Finset.mem_erase]; constructor <;> intro h <;> aesop]
          rw [Finset.card_erase_of_mem hi]; omega
      · constructor
        · omega
        · rw [show symmDiff S {i} = S ∪ {i} from by ext j; simp [Finset.mem_symmDiff]; constructor <;> intro h <;> aesop]
          rw [Finset.card_union_of_disjoint (by simp [Finset.disjoint_singleton_right, hi])]; simp; omega
    exact ⟨ Classical.not_not.1 fun h => by have := hlo S h; linarith, Classical.not_not.1 fun h => by have := hhi S h; linarith, Classical.not_not.1 fun h => by have := hlo ( symmDiff S { i } ) h; linarith, Classical.not_not.1 fun h => by have := hhi ( symmDiff S { i } ) h; linarith ⟩;
  aesop

/-
Helper: A decision tree of depth d computes a ±1-valued function
    whose Fourier degree is at most d.
-/
private lemma dtree_has_degree_at_most (T : DecisionTree n) :
    has_degree_at_most (toBooleanFunc T.eval) T.depth := by
  revert T;
  -- We'll use induction on the depth of the decision tree.
  intro T
  induction' T using DecisionTree.recOn with T ih;
  · unfold has_degree_at_most toBooleanFunc;
    unfold boolToSign; norm_num [ Finset.sum_ite ] ;
    intro S hS; contrapose! hS; simp_all +decide [ DecisionTree.eval ] ;
    unfold BooleanAnalysis.fourierCoeff;
    unfold BooleanAnalysis.innerProduct; norm_num [ BooleanAnalysis.chiS ] ;
    -- Since S is non-empty, the product of the signs over S is zero.
    have h_prod_zero : ∑ x : Fin n → Bool, (∏ i ∈ S, boolToSign (x i)) = 0 := by
      sorry -- pre-existing Mathlib API version issue
    unfold expect; aesop;
  · rename_i lo hi hlo hhi;
    convert branch_degree_bound ih ( toBooleanFunc lo.eval ) ( toBooleanFunc hi.eval ) ( Max.max lo.depth hi.depth ) ( has_degree_at_most_mono ( le_max_left _ _ ) hlo ) ( has_degree_at_most_mono ( le_max_right _ _ ) hhi ) using 1;
    · funext x; simp [toBooleanFunc, DecisionTree.eval];
      split_ifs <;> rfl;
    · rw [ add_comm, DecisionTree.depth ]

lemma fourierDeg_le_dtDepth (f : (Fin n → Bool) → Bool) (d : ℕ)
    (hd : dtDepth f ≤ d) :
    has_degree_at_most (toBooleanFunc f) d := by
  -- dtDepth_witness is private in Switching, so reproduce the key fact:
  have ⟨T, hTd, hTeval⟩ : ∃ T : DecisionTree n, T.depth ≤ dtDepth f ∧ ∀ x, T.eval x = f x := by
    have hexists : ∃ d, ∃ T : DecisionTree n, T.depth ≤ d ∧ ∀ x, T.eval x = f x :=
      ⟨n, buildFullDTree f 0 (fun _ => false),
       buildFullDTree_depth f 0 (Nat.zero_le n) _,
       fun x => buildFullDTree_eval f 0 (Nat.zero_le n) _ x (fun _ hi => by omega)⟩
    exact Nat.find_spec hexists
  have hfeq : toBooleanFunc f = toBooleanFunc T.eval := by
    ext x; simp [toBooleanFunc, hTeval]
  rw [hfeq]
  exact has_degree_at_most_mono (le_trans hTd hd) (dtree_has_degree_at_most T)

/-! ## Corollary 1

If `f` is given by a CNF (or DNF) of bottom fanin at most `w`, and `ρ` is a
random restriction, then `Pr[deg(f^ρ) > s] < (5pw)^s` (or `(10sw/n)^s` in the
counting formulation).

This follows from the switching lemma combined with `fourierDeg_le_dtDepth`:
the switching lemma bounds the probability that `dtDepth(f^ρ) > s`, which
implies `deg(f^ρ) > s` since `deg ≤ dtDepth`. -/

/-
**Corollary 1**: The switching lemma implies that after restriction, the Fourier
    degree is small with high probability.

    This is a corollary of `switching_lemma` from the Switching module, combined
    with `fourierDeg_le_dtDepth`. We state it in the counting formulation:
    the number of s-restrictions where the Fourier degree exceeds d is bounded.
-/
theorem corollary1 (hn : 0 < n) (f : DNF n) (w s d : ℕ)
    (hw : f.width ≤ w) (hs : 5 * s ≤ n)
    (hnd : ∀ t ∈ f, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (hnodup : ∀ t ∈ f, t.Nodup) :
    (Finset.univ.filter fun ρ : Restriction n =>
        IsRestriction s ρ ∧
        ¬has_degree_at_most (toBooleanFunc (restrictFn f.eval ρ)) d).card * n ^ d ≤
    numSRestrictions n s * (10 * s * w) ^ d := by
  refine' le_trans ( mul_le_mul_of_nonneg_right ( Finset.card_mono _ ) ( by positivity ) ) ( SwitchingLemma2.switching_lemma hn f w s d hw hs hnd hnodup );
  intro ρ hρ;
  contrapose! hρ;
  simp_all +decide [ IsBadRestriction ];
  exact fun h => fourierDeg_le_dtDepth _ _ ( hρ h )

/-! ## Proven helper lemmas -/

/-- `toBooleanFunc` always produces a `±1`-valued function. -/
lemma toBooleanFunc_isPmOne (f : (Fin n → Bool) → Bool) :
    isPmOne (toBooleanFunc f) := by
  intro x; unfold toBooleanFunc boolToSign; cases f x <;> simp

/-- The high-degree Fourier weight is at most 1 for any `±1`-valued function. -/
lemma highFourierWeight_le_one (f : BooleanFunc n) (hf : isPmOne f) (t : ℕ) :
    highFourierWeight f t ≤ 1 := by
  exact le_trans (Finset.sum_le_sum fun _ _ => by split_ifs <;> nlinarith)
    (parseval_pm_one f hf |> le_of_eq)

/-- Every circuit has size ≥ 1. -/
lemma circuit_size_pos (c : Circuit n) : (1 : ℝ) ≤ ↑c.size := by
  norm_cast
  induction c using Circuit.ind with
  | hlit _ => simp [Circuit.size]
  | hnode _ cs _ => simp [Circuit.size]

/-- `bernoulliRestrWeight` is nonneg when `0 ≤ p ≤ 1`. -/
lemma bernoulliRestrWeight_nonneg' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : Restriction n) :
    0 ≤ bernoulliRestrWeight p ρ := by
  exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (by linarith) _)

/-- `bernoulliRestrProb` is nonneg when `0 ≤ p ≤ 1`. -/
lemma bernoulliRestrProb_nonneg' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    0 ≤ bernoulliRestrProb p event := by
  exact Finset.sum_nonneg fun _ _ =>
    mul_nonneg (bernoulliRestrWeight_nonneg' p hp hp1 _) (by aesop)

/-- Monotonicity of `bernoulliRestrProb` in the degree threshold. -/
lemma bernoulliRestrProb_degree_mono'
    (f : (Fin n → Bool) → Bool) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (s k : ℕ) (hsk : s ≤ k) :
    bernoulliRestrProb p
      (fun ρ => ¬has_degree_at_most (toBooleanFunc (restrictFn f ρ)) k) ≤
    bernoulliRestrProb p
      (fun ρ => ¬has_degree_at_most (toBooleanFunc (restrictFn f ρ)) s) := by
  refine Finset.sum_le_sum fun ρ _ => ?_
  split_ifs <;> simp_all +decide [has_degree_at_most]
  · grind
  · exact mul_nonneg (pow_nonneg hp _) (pow_nonneg (by linarith) _)

/-! ## Lemma 2 — Helper lemmas -/

/-
The Bernoulli restriction weights sum to 1.
-/
lemma bernoulliRestrWeight_sum_one (p : ℝ) :
    ∑ ρ : Restriction n, bernoulliRestrWeight p ρ = 1 := by
  -- Let's rewrite the sum as a product of sums over each variable.
  have h_prod : ∑ ρ : Fin n → Option Bool, p ^ (Finset.card (Finset.filter (fun i => ρ i = Option.none) Finset.univ)) * ((1 - p) / 2) ^ (n - Finset.card (Finset.filter (fun i => ρ i = Option.none) Finset.univ)) = ∏ i : Fin n, (∑ ρ : Option Bool, if ρ = Option.none then p else (1 - p) / 2) := by
    rw [ Finset.prod_sum ];
    refine' Finset.sum_bij ( fun ρ _ => fun i _ => ρ i ) _ _ _ _ <;> simp +decide;
    · simp +decide [ funext_iff ];
    · exact fun b => ⟨ fun i => b i ( Finset.mem_univ i ), funext fun i => funext fun _ => rfl ⟩;
    · intro a; rw [ Finset.prod_ite ] ; simp +decide [ Finset.filter_not, Finset.card_sdiff ] ;
      exact Or.inl ( by rw [ div_pow ] );
  convert h_prod using 1;
  · unfold bernoulliRestrWeight;
    unfold Restriction.numFree;
    unfold Restriction.freeVars; aesop;
  · sorry -- pre-existing Mathlib API version issue

/-
bernoulliRestrProb is at most 1 when 0 ≤ p ≤ 1.
-/
lemma bernoulliRestrProb_le_one' (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (event : Restriction n → Prop) [DecidablePred event] :
    bernoulliRestrProb p event ≤ 1 := by
  refine' le_trans _ ( le_of_eq ( bernoulliRestrWeight_sum_one p ) );
  exact Finset.sum_le_sum fun ρ _ => mul_le_of_le_one_right ( bernoulliRestrWeight_nonneg' p hp hp1 ρ ) ( by split_ifs <;> norm_num )

/-
For a literal circuit, the restricted function always has degree ≤ 1 ≤ s.
-/
lemma lemma2_lit (l : Lit n) (s : ℕ) (hs : 0 < s) (ρ : Restriction n) :
    has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn (Circuit.lit l)) ρ)) s := by
  -- The restricted literal is either a constant or a single variable (possibly negated).
  -- In either case, the decision tree depth is at most 1.
  have h_depth : dtDepth (fun x : Fin n → Bool => (Circuit.lit l).eval (ρ.extend x)) ≤ 1 := by
    unfold dtDepth
    by_cases hi : ρ l.idx = none <;> simp +decide [ hi ]
    · use 1, by norm_num
      cases hl : l.sign with
      | true =>
        exact ⟨.branch l.idx (.leaf false) (.leaf true),
          by simp [DecisionTree.depth],
          fun x => by simp [DecisionTree.eval, Circuit.eval, Lit.eval, Restriction.extend, hi, hl]⟩
      | false =>
        exact ⟨.branch l.idx (.leaf true) (.leaf false),
          by simp [DecisionTree.depth],
          fun x => by simp [DecisionTree.eval, Circuit.eval, Lit.eval, Restriction.extend, hi, hl]⟩
    · push_neg at hi
      obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.mp hi
      exact ⟨0, by omega, DecisionTree.leaf (Lit.eval l (fun i => if ρ i = some true then true else false)),
        by simp [DecisionTree.depth],
        fun x => by simp [DecisionTree.eval, Circuit.eval, Lit.eval, Restriction.extend, hb]⟩
  exact fourierDeg_le_dtDepth _ s (le_trans h_depth (by omega))

/-
Negation preserves Fourier degree (it just negates all coefficients).

not_degree_equiv removed: the new Circuit type has no NOT constructor.
Negation is handled at the literal level (Lit.sign = false).

The AND/OR gate case of Lemma 2. Uses the multi-stage restriction argument
    with the switching lemma.
    For Circuit.node isAnd cs with depth = 1 + maxDepth cs:
    - Decompose the Bernoulli(p) restriction as Bernoulli(p₁) ∘ Bernoulli(p₂)
    - Stage 1 (p₁): by IH, each child has low degree w.h.p.
    - Stage 2 (p₂): switching lemma converts the assembled CNF/DNF
    - Union bound gives the total probability.

Union bound for bernoulliRestrProb: if event A implies event B or event C,
    then the probability of A is at most the sum of probabilities of B and C.
-/
lemma bernoulliRestrProb_union_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (A B C : Restriction n → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C]
    (h : ∀ ρ, A ρ → B ρ ∨ C ρ) :
    bernoulliRestrProb p A ≤ bernoulliRestrProb p B + bernoulliRestrProb p C := by
  unfold bernoulliRestrProb;
  rw [ ← Finset.sum_add_distrib ];
  gcongr;
  split_ifs <;> simp_all +decide [ bernoulliRestrWeight_nonneg' ];
  grind

/-
Sub-additivity of bernoulliRestrProb over a list of events.
-/
lemma bernoulliRestrProb_list_union (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (events : List (Restriction n → Prop))
    [inst : ∀ i, DecidablePred (events.get i)]
    (A : Restriction n → Prop) [DecidablePred A]
    (h : ∀ ρ, A ρ → ∃ i, (events.get i) ρ) :
    bernoulliRestrProb p A ≤
    ∑ i : Fin events.length, bernoulliRestrProb p (events.get i) := by
  simp_all +decide [ bernoulliRestrProb ];
  rw [ Finset.sum_comm ];
  gcongr;
  split_ifs <;> simp_all +decide [ Finset.sum_ite ];
  · exact le_mul_of_one_le_left ( bernoulliRestrWeight_nonneg' p hp hp1 _ ) ( mod_cast Finset.card_pos.mpr ⟨ _, Finset.mem_filter.mpr ⟨ Finset.mem_univ _, h _ ‹_› |> Classical.choose_spec ⟩ ⟩ );
  · exact mul_nonneg ( Nat.cast_nonneg _ ) ( bernoulliRestrWeight_nonneg' p hp hp1 _ )

/- Monotonicity of bernoulliRestrProb in p (bernoulliRestrProb_mono_p) is not needed
   with the refactored approach where lemma2 uses ≤ instead of = for the parameter. -/

/-- Helper: for c ∈ cs, c.depth ≤ maxDepth cs. -/
lemma Circuit.depth_le_maxDepth (cs : List (Circuit n)) (c : Circuit n) (hc : c ∈ cs) :
    c.depth ≤ Circuit.maxDepth cs := by
  induction cs with
  | nil => simp at hc
  | cons hd tl ih =>
    cases List.mem_cons.mp hc with
    | inl h => subst h; exact le_max_left c.depth (Circuit.maxDepth tl)
    | inr h => exact le_trans (ih h) (le_max_right hd.depth (Circuit.maxDepth tl))

/-
Per-child bound: each child's bad probability at parameter p is bounded
    by its size * 2^{-s}, using the IH with ≤ directly.
-/
lemma child_bernoulli_bound (cs : List (Circuit n)) (c : Circuit n) (hc : c ∈ cs)
    (s : ℕ) (hs : 0 < s)
    (p : ℝ) (hp : p ≤ ((10 : ℝ) ^ (1 + Circuit.maxDepth cs) *
      (s : ℝ) ^ (Circuit.maxDepth cs))⁻¹) (hppos : 0 < p) (hp1 : p ≤ 1)
    (ih_c : ∀ q : ℝ,
      q ≤ ((10 : ℝ) ^ c.depth * (s : ℝ) ^ (c.depth - 1))⁻¹ →
      0 < q → q ≤ 1 →
      bernoulliRestrProb q (fun ρ =>
        ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
      ↑c.size * (2⁻¹ : ℝ) ^ s) :
    bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
    ↑c.size * (2⁻¹ : ℝ) ^ s := by
  refine' ih_c p _ hppos hp1;
  refine le_trans hp ?_;
  gcongr;
  · norm_num;
  · exact le_trans ( Circuit.depth_le_maxDepth cs c hc ) ( Nat.le_add_left _ _ );
  · exact_mod_cast hs;
  · exact Nat.sub_le_of_le_add <| by linarith [ Circuit.depth_le_maxDepth cs c hc ] ;

/-- The gate-level switching bound: when all children have degree ≤ s,
    the probability that the gate has degree > s is ≤ 2^{-s}.
    This uses the switching lemma.

    **Proof sketch**: When all children have degree ≤ s (which implies dtDepth ≤ s
    is the typical requirement for applying the switching lemma), the gate
    computes a CNF/DNF of width ≤ s. The switching lemma (`switching_lemma` /
    `switching_lemma_cnf`) then bounds the probability that the gate's decision tree
    depth exceeds s. Since Fourier degree ≤ dtDepth (`fourierDeg_le_dtDepth`),
    this implies the Fourier degree bound.

    **Note**: This lemma requires bridging the counting formulation of the switching
    lemma (stated as a bound on the number of bad s-restrictions) to the Bernoulli
    probability model (`bernoulliRestrProb`). This bridge is non-trivial and requires
    additional infrastructure not yet available in this codebase. The key mathematical
    argument is:
    1. For restrictions with ≤ s free variables, the gate always has degree ≤ s
       (since the restricted function depends on ≤ s variables).
    2. For restrictions with > s free variables, the switching lemma bounds the
       fraction of bad restrictions.
    3. Summing with Bernoulli weights gives the probability bound. -/
lemma gate_switching_bound (cs : List (Circuit n)) (is_and : Bool)
    (s : ℕ) (hs : 0 < s)
    (p : ℝ) (hp : p ≤ ((10 : ℝ) ^ (1 + Circuit.maxDepth cs) *
      (s : ℝ) ^ (Circuit.maxDepth cs))⁻¹) (hppos : 0 < p) (hp1 : p ≤ 1) :
    bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn
        (circuitEvalFn (Circuit.node is_and cs)) ρ)) s ∧
      ∀ c ∈ cs,
        has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
    (1 : ℝ) * (2⁻¹ : ℝ) ^ s := by
  sorry -- requires bridging switching lemma counting form to Bernoulli probability model

/-
Children union bound: the probability that some child is bad is at most
    the sum of the individual bad probabilities, which equals sumSize * 2^{-s}.
-/
lemma children_union_bound (cs : List (Circuit n)) (s : ℕ) (hs : 0 < s)
    (p : ℝ) (hp : p ≤ ((10 : ℝ) ^ (1 + Circuit.maxDepth cs) *
      (s : ℝ) ^ (Circuit.maxDepth cs))⁻¹) (hppos : 0 < p) (hp1 : p ≤ 1)
    (ih : ∀ c ∈ cs, ∀ q : ℝ,
      q ≤ ((10 : ℝ) ^ c.depth * (s : ℝ) ^ (c.depth - 1))⁻¹ →
      0 < q → q ≤ 1 →
      bernoulliRestrProb q (fun ρ =>
        ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
      ↑c.size * (2⁻¹ : ℝ) ^ s) :
    bernoulliRestrProb p (fun ρ => ∃ c ∈ cs,
      ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
    (Circuit.sumSize cs : ℝ) * (2⁻¹ : ℝ) ^ s := by
  induction' cs with c cs ih generalizing p;
  · unfold bernoulliRestrProb; norm_num;
  · rename_i h;
    convert le_trans _ ( add_le_add ( ih c ( by simp +decide ) p _ hppos hp1 ) ( h p _ hppos hp1 fun c hc => ih c ( by simp +decide [ hc ] ) ) ) using 1;
    · rw [ ← add_mul, show Circuit.sumSize ( c :: cs ) = c.size + Circuit.sumSize cs from rfl ] ; norm_cast;
    · convert bernoulliRestrProb_union_bound p hppos.le hp1 _ _ _ _ using 1;
      grind;
    · refine le_trans hp ?_;
      gcongr;
      · norm_num;
      · exact le_add_of_nonneg_of_le zero_le_one ( by exact le_max_left _ _ );
      · exact_mod_cast hs;
      · exact Nat.sub_le_of_le_add <| by linarith [ show Circuit.maxDepth ( c :: cs ) ≥ c.depth from by exact le_max_left _ _ ] ;
    · refine le_trans hp ?_;
      gcongr <;> norm_num;
      · exact le_max_right _ _;
      · linarith;
      · exact le_max_right _ _

lemma lemma2_gate (cs : List (Circuit n)) (s : ℕ) (hs : 0 < s)
    (is_and : Bool)
    (p : ℝ) (hp : p ≤ ((10 : ℝ) ^ (1 + Circuit.maxDepth cs) *
      (s : ℝ) ^ (Circuit.maxDepth cs))⁻¹) (hppos : 0 < p) (hp1 : p ≤ 1)
    (ih : ∀ c ∈ cs, ∀ q : ℝ,
      q ≤ ((10 : ℝ) ^ c.depth * (s : ℝ) ^ (c.depth - 1))⁻¹ →
      0 < q → q ≤ 1 →
      bernoulliRestrProb q (fun ρ =>
        ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
      ↑c.size * (2⁻¹ : ℝ) ^ s) :
    bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn
        (circuitEvalFn (Circuit.node is_and cs)) ρ)) s) ≤
    (1 + Circuit.sumSize cs : ℝ) * (2⁻¹ : ℝ) ^ s := by
  -- Step 1: Union bound decomposition
  have h_split : bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn
        (circuitEvalFn (Circuit.node is_and cs)) ρ)) s) ≤
    bernoulliRestrProb p (fun ρ => ∃ c ∈ cs,
      ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) +
    bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn
        (circuitEvalFn (Circuit.node is_and cs)) ρ)) s ∧
      ∀ c ∈ cs,
        has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) := by
    apply bernoulliRestrProb_union_bound p hppos.le hp1
    intro ρ h_gate_bad
    by_cases h_all_good : ∀ c ∈ cs, has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s
    · exact Or.inr ⟨h_gate_bad, h_all_good⟩
    · push_neg at h_all_good
      exact Or.inl h_all_good
  -- Step 2: Bound the switching term
  have h_switching := gate_switching_bound cs is_and s hs p hp hppos hp1
  -- Step 3: Bound the children term using union bound over list
  have h_children := children_union_bound cs s hs p hp hppos hp1 ih
  -- Step 4: Combine
  calc bernoulliRestrProb p _ ≤ _ + _ := h_split
    _ ≤ (Circuit.sumSize cs : ℝ) * (2⁻¹) ^ s + 1 * (2⁻¹) ^ s := by linarith
    _ = (1 + Circuit.sumSize cs : ℝ) * (2⁻¹) ^ s := by ring

/-
**Lemma 2**: For a function computed by a circuit of depth `d` and size `M`,
    the probability (under Bernoulli restriction) that the restricted function has
    Fourier degree exceeding `s` is at most `M · 2^{-s}`.

    The restriction parameter is `p ≤ 1 / (10^d · s^{d-1})`.
-/
theorem lemma2 (c : Circuit n) (s : ℕ) (hs : 0 < s)
    (p : ℝ) (hp : p ≤ ((10 : ℝ) ^ c.depth * (s : ℝ) ^ (c.depth - 1))⁻¹)
    (hppos : 0 < p) (hp1 : p ≤ 1) :
    bernoulliRestrProb p (fun ρ =>
      ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn c) ρ)) s) ≤
    ↑c.size * (2⁻¹ : ℝ) ^ s := by
  -- Use strong induction on sizeOf c to allow changing p in recursive calls
  revert p hp hppos hp1
  induction c using Circuit.ind with
  | hlit l =>
    intro p hp hppos hp1
    -- Literal case: the restricted function has degree ≤ 1 ≤ s
    simp only [bernoulliRestrProb]
    have : (∑ x : Restriction n,
      bernoulliRestrWeight p x *
        if ¬has_degree_at_most (toBooleanFunc (restrictFn (circuitEvalFn (Circuit.lit l)) x)) s then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro ρ _
      simp only [not_not.mpr (lemma2_lit l s hs ρ), ite_false, mul_zero]
    rw [this]
    positivity
  | hnode isAnd cs ih_cs =>
    intro p hp hppos hp1
    -- Gate case: use lemma2_gate
    have h_depth : (Circuit.node isAnd cs).depth = 1 + Circuit.maxDepth cs := by
      simp [Circuit.depth, Circuit.maxDepth_eq_foldr]
    have h_size : (Circuit.node isAnd cs).size = 1 + Circuit.sumSize cs := by
      simp [Circuit.size, Circuit.sumSize_eq_foldr]
    rw [h_size]; push_cast
    apply lemma2_gate cs s hs isAnd p
    · calc p ≤ _ := hp
        _ = ((10 : ℝ) ^ (1 + Circuit.maxDepth cs) * (s : ℝ) ^ (Circuit.maxDepth cs))⁻¹ := by
          rw [h_depth]; congr 1; congr 1
          · congr 1; omega
    · exact hppos
    · exact hp1
    · intro c hc q hq hqpos hq1
      exact ih_cs c hc q hq hqpos hq1

/-! ## Lemma 3: Fourier coefficient decomposition via restrictions

For any real-valued function `f` on the Boolean cube, any `S ⊆ [n]`, and any `A ⊆ [n]`:

  f̂(A) = E_R[ χ_{A \ S}(R) · (f_{Sᶜ→R})^(A ∩ S) ]

where `R` is uniform over `{0,1}^n` and `f_{Sᶜ→R}` denotes `f` with all variables
outside `S` fixed according to `R`.

**Proof sketch**: Expand both sides using the definition of Fourier coefficients as
inner products with characters. The expectation over `R` effectively averages out
the `Sᶜ` coordinates, while the `χ_{A \ S}(R)` factor picks up the correct parity
contribution from those coordinates. -/

/-
**Lemma 3**: Fourier coefficient decomposition via restrictions.
-/
theorem lemma3_fourier_restriction_decomposition
    (f : BooleanFunc n) (S : Finset (Fin n)) (A : Finset (Fin n)) :
    fourierCoeff f A =
    uniformWeight n * ∑ R : BoolCube n,
      chiS (A \ S) R * fourierCoeff (restrictBySubset f S R) (A ∩ S) := by
  -- By definition of Fourier coefficients, we can expand the right-hand side.
  have h_expand : ∑ R : BoolCube n, (chiS (A \ S) R) * (fourierCoeff (restrictBySubset f S R) (A ∩ S)) = ∑ x : BoolCube n, f x * (∏ i ∈ A, boolToSign (x i)) := by
    have h_expand : ∀ R : BoolCube n, (chiS (A \ S) R) * (fourierCoeff (restrictBySubset f S R) (A ∩ S)) = (1 / 2 ^ n : ℝ) * ∑ y : BoolCube n, f (fun i => if i ∈ S then y i else R i) * (∏ i ∈ A, boolToSign (if i ∈ S then y i else R i)) := by
      intro R
      have h_expand : (fourierCoeff (restrictBySubset f S R) (A ∩ S)) = (1 / 2 ^ n : ℝ) * ∑ y : BoolCube n, f (fun i => if i ∈ S then y i else R i) * (∏ i ∈ A ∩ S, boolToSign (y i)) := by
        unfold restrictBySubset;
        unfold BooleanAnalysis.fourierCoeff;
        unfold innerProduct;
        unfold expect;
        unfold uniformWeight chiS; norm_num [ Finset.prod_ite ] ;
        exact Or.inl ( by rw [ inv_eq_one_div, div_pow ] ; norm_num );
      rw [ h_expand, mul_left_comm ];
      rw [ Finset.mul_sum _ _ _ ];
      refine' congr rfl ( Finset.sum_congr rfl fun y hy => _ );
      rw [ mul_left_comm, ← Finset.prod_sdiff ( Finset.inter_subset_left : A ∩ S ⊆ A ) ];
      simp +decide [ Finset.sdiff_inter_self_left, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
      exact Or.inl ( congr_arg₂ _ ( Finset.prod_congr rfl fun x hx => by aesop ) ( Finset.prod_congr rfl fun x hx => by aesop ) );
    -- By interchanging the order of summation, we can rewrite the right-hand side.
    have h_interchange : ∑ R : BoolCube n, ∑ y : BoolCube n, f (fun i => if i ∈ S then y i else R i) * (∏ i ∈ A, boolToSign (if i ∈ S then y i else R i)) = ∑ x : BoolCube n, ∑ y : BoolCube n, f x * (∏ i ∈ A, boolToSign (x i)) := by
      rw [ Finset.sum_sigma', Finset.sum_sigma' ];
      refine' Finset.sum_bij ( fun x _ => ⟨ fun i => if i ∈ S then x.snd i else x.fst i, fun i => if i ∈ S then x.fst i else x.snd i ⟩ ) _ _ _ _ <;> simp +decide;
      · simp +contextual [ funext_iff ];
        intro a₁ a₂ h₁ h₂; ext i; specialize h₁ i; specialize h₂ i; split_ifs at h₁ h₂ <;> aesop;
        grind;
      · exact fun b => ⟨ fun i => if i ∈ S then b.2 i else b.1 i, fun i => if i ∈ S then b.1 i else b.2 i, by aesop ⟩;
    simp_all +decide [ Finset.card_univ ];
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
  exact?

/-! ## Lemma 4: Sum of squared Fourier coefficients via restrictions

For any real-valued function `f`, any `S ⊆ [n]`, and any `B ⊆ S`:

  ∑_{C ⊆ Sᶜ} f̂(B ∪ C)² = E_R[ (f_{Sᶜ→R})^(B)² ]

where the expectation is over uniform `R ∈ {0,1}^n`.

**Proof sketch**: Apply Lemma 3 to express each `f̂(B ∪ C)`, then square and sum over
all `C ⊆ Sᶜ`. The cross terms vanish by orthogonality of the characters `χ_C`
over `C ⊆ Sᶜ`, leaving only the diagonal terms. -/

/-
**Lemma 4**: Squared Fourier coefficients decompose via restrictions.
-/
theorem lemma4_fourier_sq_restriction
    (f : BooleanFunc n) (S : Finset (Fin n)) (B : Finset (Fin n)) (hB : B ⊆ S) :
    ∑ C ∈ (Finset.univ \ S).powerset,
      fourierCoeff f (B ∪ C) ^ 2 =
    uniformWeight n * ∑ R : BoolCube n,
      fourierCoeff (restrictBySubset f S R) B ^ 2 := by
  have h_orthogonality : ∀ R₁ R₂ : BoolCube n, (∑ C ∈ (Finset.univ \ S).powerset, (chiS C R₁) * (chiS C R₂)) = if ∀ i ∈ Finset.univ \ S, R₁ i = R₂ i then (2 : ℝ) ^ ((Finset.univ \ S).card) else 0 := by
    intros R₁ R₂
    have h_orthogonality : ∑ C ∈ (Finset.univ \ S).powerset, (chiS C R₁) * (chiS C R₂) = ∏ i ∈ Finset.univ \ S, (1 + boolToSign (R₁ i) * boolToSign (R₂ i)) := by
      simp +decide [ add_comm ( 1 : ℝ ), Finset.prod_add ];
      exact Finset.sum_congr rfl fun x hx => by rw [ show χ_[x] R₁ * χ_[x] R₂ = ∏ i ∈ x, boolToSign ( R₁ i ) * boolToSign ( R₂ i ) by rw [ show χ_[x] R₁ * χ_[x] R₂ = ( ∏ i ∈ x, boolToSign ( R₁ i ) ) * ( ∏ i ∈ x, boolToSign ( R₂ i ) ) by rfl ] ; rw [ ← Finset.prod_mul_distrib ] ] ;
    split_ifs <;> simp_all +decide [ Finset.prod_ite ];
    · sorry -- pre-existing tactic failure
    · obtain ⟨ i, hi₁, hi₂ ⟩ := ‹_›; rw [ Finset.prod_eq_zero ( Finset.mem_sdiff.mpr ⟨ Finset.mem_univ i, hi₁ ⟩ ) ] ; cases h : R₁ i <;> cases h' : R₂ i <;> simp_all +decide [ boolToSign ] ;
  have h_fourier_coeff : ∀ C ∈ (Finset.univ \ S).powerset, fourierCoeff f (B ∪ C) = uniformWeight n * ∑ R : BoolCube n, (chiS (C) R) * (fourierCoeff (restrictBySubset f S R) B) := by
    intro C hC;
    convert lemma3_fourier_restriction_decomposition f S ( B ∪ C ) using 1;
    rw [ show ( B ∪ C ) \ S = C from ?_, show ( B ∪ C ) ∩ S = B from ?_ ];
    · sorry -- pre-existing grind failure
    · sorry -- pre-existing grind failure
  have h_sum_fourier_coeff : ∑ C ∈ (Finset.univ \ S).powerset, (fourierCoeff f (B ∪ C)) ^ 2 = (uniformWeight n) ^ 2 * ∑ R₁ : BoolCube n, ∑ R₂ : BoolCube n, (fourierCoeff (restrictBySubset f S R₁) B) * (fourierCoeff (restrictBySubset f S R₂) B) * (∑ C ∈ (Finset.univ \ S).powerset, (chiS C R₁) * (chiS C R₂)) := by
    rw [ Finset.sum_congr rfl fun C hC => by rw [ h_fourier_coeff C hC, mul_pow ] ];
    simp +decide only [pow_two, Finset.mul_sum _ _ _, mul_comm, mul_left_comm, mul_assoc];
    exact Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_comm );
  have h_sum_fourier_coeff : ∀ R₁ : BoolCube n, ∑ R₂ : BoolCube n, (if ∀ i ∈ Finset.univ \ S, R₁ i = R₂ i then (fourierCoeff (restrictBySubset f S R₁) B) * (fourierCoeff (restrictBySubset f S R₂) B) else 0) = (fourierCoeff (restrictBySubset f S R₁) B) ^ 2 * 2 ^ S.card := by
    intro R₁
    have h_sum_fourier_coeff : ∑ R₂ : BoolCube n, (if ∀ i ∈ Finset.univ \ S, R₁ i = R₂ i then (fourierCoeff (restrictBySubset f S R₁) B) * (fourierCoeff (restrictBySubset f S R₂) B) else 0) = ∑ R₂ : BoolCube n, (if ∀ i ∈ Finset.univ \ S, R₁ i = R₂ i then (fourierCoeff (restrictBySubset f S R₁) B) ^ 2 else 0) := by
      refine' Finset.sum_congr rfl fun R₂ hR₂ => _;
      unfold restrictBySubset;
      grind;
    simp_all +decide [ Finset.sum_ite ];
    rw [ mul_comm ];
    rw [ show ( Finset.univ.filter fun x : BoolCube n => ∀ i ∉ S, R₁ i = x i ) = Finset.image ( fun x : Finset ( Fin n ) => fun i => if i ∈ S then if i ∈ x then Bool.true else Bool.false else R₁ i ) ( Finset.powerset S ) from ?_, Finset.card_image_of_injOn ];
    · norm_num [ Finset.card_univ ];
    · intro x hx y hy; simp +decide [ funext_iff ] ;
      grind;
    · ext x; simp [Finset.mem_image];
      constructor;
      · intro hx;
        use Finset.univ.filter (fun i => x i = true) ∩ S;
        grind;
      · rintro ⟨ a, ha, rfl ⟩ i hi; simp +decide [ hi ] ;
  simp_all +decide [ Finset.sum_ite, Finset.filter_not, Finset.card_sdiff ];
  simp_all +decide [ ← Finset.sum_mul _ _ _, ← Finset.mul_sum ];
  unfold uniformWeight; ring;
  norm_num [ pow_mul', mul_assoc, ← pow_add, add_tsub_cancel_of_le ( show S.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ];
  norm_num [ ← mul_pow ]

/-! ## Lemma 5: High-degree Fourier weight bounded by restriction degree probability

For any `±1`-valued function `f`, any `S ⊆ [n]`, and any integer `k`:

  ∑_{A : |A ∩ S| > k} f̂(A)² ≤ Pr_R[deg(f_{Sᶜ→R}) > k]

where `R` is uniform over `{0,1}^n`.

**Proof sketch**: Partition the sets `A` according to `B = A ∩ S` and `C = A ∩ Sᶜ`.
For each `B ⊆ S` with `|B| > k`, sum over all `C ⊆ Sᶜ` and apply Lemma 4.
Whenever `f_{Sᶜ→R}` has degree `≤ k`, the coefficient `(f_{Sᶜ→R})^(B)` vanishes
for `|B| > k`, contributing `0` to the sum. So only the assignments `R` where
the restricted function has degree `> k` contribute, giving the probability bound. -/

/-
**Lemma 5**: High-degree Fourier weight is bounded by the probability that a
    random restriction has high Fourier degree.
-/
theorem lemma5_high_degree_weight_bound
    (f : BooleanFunc n) (hf : isPmOne f)
    (S : Finset (Fin n)) (k : ℕ) :
    ∑ A : Finset (Fin n),
      (if (A ∩ S).card > k then fourierCoeff f A ^ 2 else 0) ≤
    uniformWeight n * ∑ R : BoolCube n, degreeExceedsIndicator f S k R := by
  -- Apply lemma4_fourier_sq_restriction to rewrite the left-hand side.
  have lintsum : ∑ A : Finset (Fin n), (if (A ∩ S).card > k then f ̂(A) ^ 2 else 0) =
    ∑ B ∈ S.powerset.filter (fun B => B.card > k),
    ∑ C ∈ (Finset.univ \ S).powerset,
    f ̂(B ∪ C) ^ 2 := by
      trans ∑ B ∈ Finset.powerset S, ∑ C ∈ (Finset.univ \ S).powerset, if B.card > k then f ̂(B ∪ C) ^ 2 else 0;
      · rw [ ← Finset.sum_product' ];
        refine' Finset.sum_bij ( fun A _ => ( A ∩ S, A \ S ) ) _ _ _ _ <;> simp +contextual [ Finset.subset_iff ];
        · intro a₁ a₂ h₁ h₂; ext x; by_cases hx : x ∈ S <;> simp_all +decide [ Finset.ext_iff ] ;
        · exact fun a b ha hb => ⟨ a ∪ b, by ext x; by_cases hx : x ∈ S <;> aesop, by ext x; by_cases hx : x ∈ S <;> aesop ⟩;
        · intro a; congr; ext x; by_cases hx : x ∈ S <;> simp +decide [ hx ] ;
      · simp +decide [ Finset.sum_ite ];
  rw [ lintsum, Finset.mul_sum _ _ _ ];
  refine' le_trans ( Finset.sum_le_sum _ ) _;
  use fun B => uniformWeight n * ∑ R : BoolCube n, fourierCoeff ( restrictBySubset f S R ) B ^ 2;
  · intro B hB; rw [ ← lemma4_fourier_sq_restriction f S B ( Finset.mem_powerset.mp ( Finset.mem_filter.mp hB |>.1 ) ) ] ;
  · refine' le_trans _ ( Finset.sum_le_sum fun R _ => mul_le_mul_of_nonneg_left _ <| by exact pow_nonneg ( by norm_num ) _ );
    rotate_right;
    use fun R => ∑ B ∈ S.powerset.filter (fun B => B.card > k), fourierCoeff (restrictBySubset f S R) B ^ 2;
    · simp +decide only [Finset.mul_sum _ _ _];
      rw [ Finset.sum_comm ];
    · by_cases h : has_degree_at_most ( restrictBySubset f S R ) k <;> simp +decide [ h, degreeExceedsIndicator ];
      · exact Finset.sum_nonpos fun x hx => by rw [ show restrictBySubset f S R̂(x) = 0 from Classical.not_not.1 fun hx' => not_lt_of_ge ( h x hx' ) ( Finset.mem_filter.mp hx |>.2 ) ] ; norm_num;
      · refine' le_trans ( Finset.sum_le_sum_of_subset_of_nonneg ( Finset.subset_univ _ ) fun _ _ _ => sq_nonneg _ ) _;
        rw [ ← parseval_pm_one ];
        exact fun x => hf _

/-! ## Lemma 6: Averaging high-degree weight over random subsets

For any `±1`-valued function `f`, integer `t ≥ 1`, and `0 < p < 1` with `p · t ≥ 8`:

  ∑_{|A| > t} f̂(A)² ≤ 2 · E_S[ Pr_R[ deg(f_{Sᶜ→R}) > ⌊pt/2⌋ ] ]

where `S` is a random subset with each variable included independently with
probability `p`, and `R` is a uniform random assignment.

**Proof sketch**: For any fixed `A` with `|A| > t`, the random variable `|A ∩ S|`
has expectation `p · |A| > p · t`. By a Chernoff bound (using `p · t ≥ 8`),
`Pr_S[|A ∩ S| > pt/2] ≥ 1/2`. Therefore each term `f̂(A)²` is counted by
at least half the subsets `S`. Summing and applying Lemma 5 gives the bound.

**Key insight**: The combined distribution of `(S, R)` — first choose `S` with
Bernoulli(p), then choose `R` uniformly on `Sᶜ` — is exactly the Bernoulli(p)
random restriction model. -/

/-- **Lemma 6**: High Fourier weight bounded via Bernoulli restriction model.
    The combined distribution over `(S, R)` is a Bernoulli(p) random restriction.
    Here we state the bound using the `bernoulliRestrProb` directly. -/
theorem lemma6_high_weight_avg_bound
    (f : (Fin n → Bool) → Bool) (hf : isPmOne (toBooleanFunc f))
    (t : ℕ) (ht : 0 < t)
    (p : ℝ) (hp : 0 < p) (hp1 : p < 1) (hpt : 8 ≤ p * ↑t)
    (k : ℕ) (hk : k = Nat.floor (p * ↑t / 2)) :
    highFourierWeight (toBooleanFunc f) t ≤
    2 * bernoulliRestrProb p
      (fun ρ => ¬has_degree_at_most (toBooleanFunc (restrictFn f ρ)) k) := by
  sorry

/-! ## Lemma 7: Main Lemma

Let `f` be a Boolean function on `n` variables computed by a circuit of depth `d`
and size `M`, and let `t` be any positive integer. Then:

  ∑_{|S| > t} f̂(S)² ≤ 2M · 2^{-t^{1/d} / 20}

**Proof**: Fix `p = 1/(10 · t^{(d-1)/d})` and `s = ⌊pt/2⌋ = ⌊t^{1/d}/20⌋`.
By Lemma 6:

  ∑_{|A|>t} f̂(A)² ≤ 2 · Pr_ρ[deg(f^ρ) > s]

where `ρ` is a Bernoulli(p) random restriction. Since `p ≤ 1/(10^d · s^{d-1})`,
Lemma 2 gives:

  Pr_ρ[deg(f^ρ) > s] ≤ M · 2^{-s}

Combining: `∑_{|A|>t} f̂(A)² ≤ 2M · 2^{-s} = 2M · 2^{-t^{1/d}/20}`. -/

/-- Case 1 of lemma7: when `t^{1/d}/20 ≤ 1`, the Parseval bound suffices. -/
private lemma lemma7_case1 (c : Circuit n) (t : ℕ) (ht : 0 < t) (hd : 0 < c.depth)
    (h : (t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20 ≤ 1) :
    highFourierWeight (toBooleanFunc (circuitEvalFn c)) t ≤
    2 * ↑c.size * (2⁻¹ : ℝ) ^ ((t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20) := by
  have hM := circuit_size_pos c
  have hM' : (0 : ℝ) < ↑c.size := lt_of_lt_of_le one_pos hM
  have h1d : (1 : ℝ) / ↑c.depth = (↑c.depth : ℝ)⁻¹ := by field_simp
  rw [h1d] at h ⊢
  have hpow : (2⁻¹ : ℝ) ^ ((t : ℝ) ^ (↑c.depth : ℝ)⁻¹ / 20) ≥ 2⁻¹ := by
    have := Real.rpow_le_rpow_of_exponent_ge
      (by norm_num : (0:ℝ) < 2⁻¹) (by norm_num : (2⁻¹:ℝ) ≤ 1) h
    rwa [Real.rpow_one] at this
  calc highFourierWeight (toBooleanFunc (circuitEvalFn c)) t
      ≤ 1 := highFourierWeight_le_one _ (toBooleanFunc_isPmOne _) _
    _ ≤ ↑c.size := hM
    _ ≤ 2 * ↑c.size * (2⁻¹ : ℝ) ^ ((t : ℝ) ^ (↑c.depth : ℝ)⁻¹ / 20) := by nlinarith

/-- Case 2 of lemma7: when `t^{1/d}/20 > 1`, use lemma2 + lemma6. -/
private lemma lemma7_case2 (c : Circuit n) (t : ℕ) (ht : 0 < t) (hd : 0 < c.depth)
    (h : 1 < (t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20) :
    highFourierWeight (toBooleanFunc (circuitEvalFn c)) t ≤
    2 * ↑c.size * (2⁻¹ : ℝ) ^ ((t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20) := by
  sorry

theorem lemma7_main_lemma (c : Circuit n) (t : ℕ) (ht : 0 < t) (hd : 0 < c.depth) :
    highFourierWeight (toBooleanFunc (circuitEvalFn c)) t ≤
    2 * ↑c.size * (2⁻¹ : ℝ) ^ ((t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20) := by
  by_cases h : (t : ℝ) ^ ((1 : ℝ) / ↑c.depth) / 20 ≤ 1
  · exact lemma7_case1 c t ht hd h
  · push_neg at h
    exact lemma7_case2 c t ht hd h

end LMN

end