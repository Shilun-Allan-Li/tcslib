/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TCSlib.Complexity.Randomized.RandomBits
import TCSlib.Complexity.Randomized.SchwartzZippel

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Perfect matchings, the Edmonds matrix, and Lovász's test

The mathematical half of [AB09, §7.2.4]: a bipartite graph `G` on `[n] ⊔ [n]`, given by a
Boolean `n × n` adjacency matrix `A`, has a perfect matching iff the determinant of its Edmonds
matrix `X` (`X_{ij} = x_{ij}` if `ij ∈ E`, else `0`) is a nonzero polynomial; substituting
random values from a set of size `≥ 2n` (Lovász) gives a nonzero determinant with
probability `≥ 1/2` when a matching exists, and always `0` when none exists.

The official notion is the book's own (an edge set meeting every vertex exactly once, i.e.
Mathlib's `Subgraph.IsPerfectMatching`); the book's permutation view is proved equivalent and
is what the determinant argument uses.

## Main definitions

* `Randomized.Matching.bipartiteGraph`, `Randomized.Matching.HasPerfectMatching` — the graph
  and the book's notion (Mathlib's `Subgraph.IsPerfectMatching`).
* `Randomized.Matching.edmondsMatrix` — `X` over `MvPolynomial (Fin n × Fin n) R`.
* `Randomized.Matching.lovaszMatrix`, `Randomized.Matching.lovaszSample` — `X` at a point;
  the point read off a coin word, `k` coins per entry.

## Main results (namespace `Randomized.Matching`)

* `hasPerfectMatching_iff_exists_perm` — matchings are permutations `σ` with `A i (σ i)`.
* `det_edmondsMatrix_ne_zero_iff` — `G` has a perfect matching ⇔ `det X ≠ 0` (any nontrivial
  commutative ring, e.g. `ℤ`, `ZMod p`); `totalDegree_det_edmondsMatrix_le` — degree `≤ n`.
* `lovasz_test`, `lovasz_test_int`, `lovasz_test_zmod` — `Pr[det ≠ 0] ≥ 1/2` given a matching;
  `randProb_lovasz_eq_zero` — probability `0` without one.

## Divergences

* The book's "real variables" become `MvPolynomial (Fin n × Fin n) R` for any nontrivial
  commutative ring `R`; the coefficients of `det X` are `±1` on distinct monomials, so the
  characterization holds over `ℤ` and every `ZMod p` alike.
* The book samples from `[2n]`. Coins only give power-of-two ranges, so each entry reads
  `k` fair coins as a number in `{0, …, 2^k - 1}` with `2^k ≥ 2n` (e.g. `k = ⌈log₂ 2n⌉`);
  [AB09, Lemma 7.5] only needs `|S| ≥ 2n`. Over `ZMod p` (the prime-field variant used for
  the class-level algorithm) we need `2^k ≤ p` so the `2^k` values stay distinct; the prime
  comes from Bertrand.
* Probabilities are `Randomized.randProb` counting ratios; coins past the first `n²k` are
  ignored, so the bound holds for every coin-word length `m ≥ n²k`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

namespace Randomized.Matching

open MvPolynomial Finset Equiv

variable {n : ℕ}

/-! ### Bipartite graphs and perfect matchings -/

/-- The bipartite graph on `[n] ⊔ [n]` with adjacency matrix `A`: left vertex `i` and right
vertex `j` are adjacent iff `A i j` [AB09, §7.2.4]. -/
def bipartiteGraph (A : Matrix (Fin n) (Fin n) Bool) : SimpleGraph (Fin n ⊕ Fin n) where
  Adj u v := match u, v with
    | .inl i, .inr j => A i j = true
    | .inr j, .inl i => A i j = true
    | _, _ => False
  symm u v h := by cases u <;> cases v <;> simp_all
  loopless u h := by cases u <;> simp_all

/-- Left `i` and right `j` are adjacent iff `A i j`. -/
@[simp] theorem bipartiteGraph_adj_inl_inr (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) :
    (bipartiteGraph A).Adj (.inl i) (.inr j) ↔ A i j = true := Iff.rfl

/-- Right `j` and left `i` are adjacent iff `A i j`. -/
@[simp] theorem bipartiteGraph_adj_inr_inl (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) :
    (bipartiteGraph A).Adj (.inr j) (.inl i) ↔ A i j = true := Iff.rfl

/-- No two left vertices are adjacent. -/
@[simp] theorem not_bipartiteGraph_adj_inl_inl (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) :
    ¬ (bipartiteGraph A).Adj (.inl i) (.inl j) := id

/-- No two right vertices are adjacent. -/
@[simp] theorem not_bipartiteGraph_adj_inr_inr (A : Matrix (Fin n) (Fin n) Bool) (i j : Fin n) :
    ¬ (bipartiteGraph A).Adj (.inr i) (.inr j) := id

/-- `A`'s bipartite graph has a perfect matching: a set of edges meeting every vertex exactly
once [AB09, §7.2.4]. -/
def HasPerfectMatching (A : Matrix (Fin n) (Fin n) Bool) : Prop :=
  ∃ M : (bipartiteGraph A).Subgraph, M.IsPerfectMatching

/-- A perfect matching is a permutation `σ` of `[n]` with every `i (σ i)` an edge
[AB09, §7.2.4: "we may think of `E'` as a permutation `σ`"].

**Proof sketch.** A perfect matching sends each left `i` to a unique right `f i`; `f` is
injective because right vertices are matched once, hence a permutation of the finite `[n]`.
Conversely the graph of `σ` is a spanning subgraph in which every vertex has one partner. -/
theorem hasPerfectMatching_iff_exists_perm (A : Matrix (Fin n) (Fin n) Bool) :
    HasPerfectMatching A ↔ ∃ σ : Perm (Fin n), ∀ i, A i (σ i) = true := by
  constructor
  · rintro ⟨M, hM⟩
    have h1 := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hM
    have hex : ∀ i, ∃ j, M.Adj (.inl i) (.inr j) := by
      intro i
      obtain ⟨w, hw, -⟩ := h1 (.inl i)
      cases w with
      | inl j => exact absurd (M.adj_sub hw) (not_bipartiteGraph_adj_inl_inl A i j)
      | inr j => exact ⟨j, hw⟩
    choose f hf using hex
    have hinj : Function.Injective f := by
      intro i i' h
      obtain ⟨w, -, hw⟩ := h1 (.inr (f i))
      have e1 := hw _ (M.symm (hf i))
      have e2 := hw _ (M.symm (h ▸ hf i'))
      exact Sum.inl_injective (e1.trans e2.symm)
    refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), fun i => ?_⟩
    exact M.adj_sub (hf i)
  · rintro ⟨σ, hσ⟩
    let P : Matrix (Fin n) (Fin n) Bool := Matrix.of fun i j => decide (σ i = j)
    let H := bipartiteGraph P
    have hle : H ≤ bipartiteGraph A := by
      intro u v h
      cases u with
      | inl i => cases v with
        | inl j => exact absurd h (not_bipartiteGraph_adj_inl_inl _ i j)
        | inr j =>
          have : σ i = j := by simpa [H, P] using h
          subst this; exact hσ i
      | inr j => cases v with
        | inl i =>
          have : σ i = j := by simpa [H, P] using h
          subst this; exact hσ i
        | inr j' => exact absurd h (not_bipartiteGraph_adj_inr_inr _ j j')
    refine ⟨@SimpleGraph.toSubgraph _ (bipartiteGraph A) H hle,
      SimpleGraph.Subgraph.isPerfectMatching_iff.mpr fun v => ?_⟩
    cases v with
    | inl i =>
      refine ⟨.inr (σ i), by simp [H, P], fun w hw => ?_⟩
      cases w with
      | inl j => exact absurd hw (not_bipartiteGraph_adj_inl_inl P i j)
      | inr j =>
        have : σ i = j := by simpa [H, P] using hw
        rw [this]
    | inr j =>
      refine ⟨.inl (σ.symm j), by simp [H, P], fun w hw => ?_⟩
      cases w with
      | inl i =>
        have : σ i = j := by simpa [H, P] using hw
        rw [← this, Equiv.symm_apply_apply]
      | inr j' =>
        exact absurd hw (not_bipartiteGraph_adj_inr_inr P j j')

/-! ### The Edmonds matrix -/

/-- The Edmonds matrix `X`: `X_{ij} = x_{ij}` if `ij` is an edge, else `0`
[AB09, §7.2.4]. -/
noncomputable def edmondsMatrix (R : Type*) [CommSemiring R] (A : Matrix (Fin n) (Fin n) Bool) :
    Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) R) :=
  Matrix.of fun i j => if A i j then X (i, j) else 0

/-- The exponent vector `∑ᵢ e_{(i, σ i)}` of the monomial `∏ᵢ x_{i,σ(i)}`. -/
private noncomputable def matchMono (σ : Perm (Fin n)) : Fin n × Fin n →₀ ℕ :=
  ∑ i, Finsupp.single (i, σ i) 1

/-- `∑ᵢ e_{(i, σ i)}` has entry `1` at `(a, σ a)` and `0` elsewhere. -/
private theorem matchMono_apply (σ : Perm (Fin n)) (a b : Fin n) :
    matchMono σ (a, b) = if σ a = b then 1 else 0 := by
  classical
  simp only [matchMono, Finsupp.finset_sum_apply, Finsupp.single_apply, Prod.ext_iff]
  rw [Finset.sum_eq_single a (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- Distinct permutations give distinct monomials. -/
private theorem matchMono_injective : Function.Injective (matchMono (n := n)) := by
  intro σ τ h
  refine Equiv.ext fun a => ?_
  have h1 : matchMono τ (a, σ a) = 1 := by rw [← h, matchMono_apply, if_pos rfl]
  rw [matchMono_apply] at h1
  split_ifs at h1 with h'
  exact h'.symm

/-- `∏ᵢ X_{i,σ(i)}` is the monomial of `σ` if `σ` uses only edges, else `0`. -/
private theorem prod_edmondsMatrix (R : Type*) [CommSemiring R] (A : Matrix (Fin n) (Fin n) Bool)
    (σ : Perm (Fin n)) [Decidable (∀ i, A i (σ i) = true)] :
    ∏ i, edmondsMatrix R A i (σ i) =
      if ∀ i, A i (σ i) = true then monomial (matchMono σ) 1 else 0 := by
  split_ifs with h
  · simp only [edmondsMatrix, Matrix.of_apply, h, if_true, X, matchMono, monomial_sum_one]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (mem_univ i) (by simp [edmondsMatrix, hi])

/-- The Leibniz expansion of `det X` along rows. -/
private theorem det_edmondsMatrix_eq_sum (R : Type*) [CommRing R]
    (A : Matrix (Fin n) (Fin n) Bool) :
    (edmondsMatrix R A).det =
      ∑ σ : Perm (Fin n), ((Perm.sign σ : ℤ) : MvPolynomial (Fin n × Fin n) R) *
        ∏ i, edmondsMatrix R A i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

/-- Without a perfect matching `det X = 0`, over any commutative ring. -/
theorem det_edmondsMatrix_eq_zero (R : Type*) [CommRing R] (A : Matrix (Fin n) (Fin n) Bool)
    (hA : ¬ HasPerfectMatching A) : (edmondsMatrix R A).det = 0 := by
  classical
  rw [hasPerfectMatching_iff_exists_perm] at hA
  push_neg at hA
  rw [det_edmondsMatrix_eq_sum]
  refine Finset.sum_eq_zero fun σ _ => ?_
  obtain ⟨i, hi⟩ := hA σ
  rw [Finset.prod_eq_zero (mem_univ i) (by simp [edmondsMatrix, hi]), mul_zero]

/-- The coefficient of `∏ᵢ x_{i,τ(i)}` in `det X` is `sgn τ` when `τ` uses only edges. -/
private theorem coeff_det_edmondsMatrix (R : Type*) [CommRing R] (A : Matrix (Fin n) (Fin n) Bool)
    (τ : Perm (Fin n)) (hτ : ∀ i, A i (τ i) = true) :
    coeff (matchMono τ) (edmondsMatrix R A).det = ((Perm.sign τ : ℤ) : R) := by
  classical
  rw [det_edmondsMatrix_eq_sum, coeff_sum]
  rw [Finset.sum_eq_single τ]
  · rw [prod_edmondsMatrix, if_pos hτ, ← map_intCast (C : R →+* MvPolynomial _ R), coeff_C_mul,
      coeff_monomial, if_pos rfl, mul_one]
  · intro σ _ hστ
    rw [prod_edmondsMatrix, ← map_intCast (C : R →+* MvPolynomial _ R), coeff_C_mul]
    split_ifs with h
    · rw [coeff_monomial, if_neg (fun h' => hστ (matchMono_injective h')), mul_zero]
    · rw [coeff_zero, mul_zero]
  · simp

/-- `G` has a perfect matching iff `det X` is not the zero polynomial [AB09, §7.2.4].

**Proof sketch.** `det X = ∑_σ sgn σ ∏ᵢ X_{i,σ(i)}`; a term is nonzero iff `σ` is a matching,
and then it is `± ∏ᵢ x_{i,σ(i)}`. These monomials differ for different `σ`, so a matching `τ`
leaves coefficient `sgn τ = ±1 ≠ 0`; with no matching every term vanishes. -/
theorem det_edmondsMatrix_ne_zero_iff (R : Type*) [CommRing R] [Nontrivial R]
    (A : Matrix (Fin n) (Fin n) Bool) :
    (edmondsMatrix R A).det ≠ 0 ↔ HasPerfectMatching A := by
  refine ⟨fun h => by_contra fun hA => h (det_edmondsMatrix_eq_zero R A hA), fun hA h0 => ?_⟩
  obtain ⟨τ, hτ⟩ := (hasPerfectMatching_iff_exists_perm A).mp hA
  have hc := coeff_det_edmondsMatrix R A τ hτ
  rw [h0, coeff_zero] at hc
  rcases Int.units_eq_one_or (Perm.sign τ) with hs | hs <;> rw [hs] at hc <;> simp at hc

/-- `det X` has total degree at most `n` [AB09, §7.2.4]. -/
theorem totalDegree_det_edmondsMatrix_le (R : Type*) [CommRing R]
    (A : Matrix (Fin n) (Fin n) Bool) :
    (edmondsMatrix R A).det.totalDegree ≤ n := by
  rw [det_edmondsMatrix_eq_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun σ _ => ?_)
  refine (totalDegree_mul _ _).trans ?_
  rw [← map_intCast (C : R →+* MvPolynomial _ R), totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans ?_
  calc ∑ i, (edmondsMatrix R A i (σ i)).totalDegree ≤ ∑ _i : Fin n, 1 := by
        refine Finset.sum_le_sum fun i _ => ?_
        simp only [edmondsMatrix, Matrix.of_apply]
        split_ifs
        · exact (totalDegree_monomial_le _ _).trans (by simp)
        · simp
    _ = n := by simp

/-! ### Evaluation: Lovász's matrix -/

/-- `X` evaluated at `a`: entry `a (i, j)` on edges and `0` elsewhere [AB09, §7.2.4]. -/
def lovaszMatrix {R : Type*} [Zero R] (A : Matrix (Fin n) (Fin n) Bool) (a : Fin n × Fin n → R) :
    Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j => if A i j then a (i, j) else 0

/-- Evaluating `det X` at `a` is the determinant of `X` evaluated at `a`. -/
theorem eval_det_edmondsMatrix {R : Type*} [CommRing R] (A : Matrix (Fin n) (Fin n) Bool)
    (a : Fin n × Fin n → R) :
    eval a (edmondsMatrix R A).det = (lovaszMatrix A a).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, edmondsMatrix, lovaszMatrix,
    Matrix.of_apply]
  split_ifs <;> simp

/-- Without a perfect matching every substitution has determinant `0` [AB09, §7.2.4]. -/
theorem det_lovaszMatrix_eq_zero {R : Type*} [CommRing R]
    (A : Matrix (Fin n) (Fin n) Bool) (hA : ¬ HasPerfectMatching A) (a : Fin n × Fin n → R) :
    (lovaszMatrix A a).det = 0 := by
  rw [← eval_det_edmondsMatrix, det_edmondsMatrix_eq_zero R A hA, map_zero]

/-! ### Lovász's test -/

/-- Lovász's random point: entry `(i, j)` is block `n·i + j` of `k` coins (`blockVal`),
cast to `R`. -/
def lovaszSample (R : Type*) [NatCast R] (n k : ℕ) (l : List Bool) : Fin n × Fin n → R :=
  fun ij => (blockVal k l (finProdFinEquiv ij) : R)

/-- Lovász's test with exactly `n²k` coins.

**Proof sketch.** Rename the variables of `det X` along `[n] × [n] ≃ [n²]` to get `q ≠ 0` of
degree `≤ n`. The accepted coin words correspond (via `randProb_blocks_piFinset` and the cast
`{0, …, 2^k - 1} ↪ R`) to the non-zeros of `q` on `S^{n²}`, `|S| = 2^k ≥ 2n`; Schwartz–Zippel
leaves at most half of `S^{n²}` as zeros. -/
private theorem lovasz_test_exact {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (A : Matrix (Fin n) (Fin n) Bool) (hA : HasPerfectMatching A) {k : ℕ} (hk : 2 * n ≤ 2 ^ k)
    (hinj : Set.InjOn (Nat.cast : ℕ → R) (range (2 ^ k))) :
    1 / 2 ≤ randProb (n * n * k) fun l => (lovaszMatrix A (lovaszSample R n k l)).det ≠ 0 := by
  classical
  set q : MvPolynomial (Fin (n * n)) R := rename finProdFinEquiv (edmondsMatrix R A).det
  set S : Finset R := (range (2 ^ k)).image (Nat.cast : ℕ → R)
  have hS : #S = 2 ^ k := by rw [card_image_of_injOn hinj, card_range]
  have hq : q ≠ 0 := fun h0 =>
    (det_edmondsMatrix_ne_zero_iff R A).mpr hA
      (rename_injective _ finProdFinEquiv.injective (h0.trans (map_zero _).symm))
  have hdeg : q.totalDegree ≤ n :=
    (totalDegree_rename_le _ _).trans (totalDegree_det_edmondsMatrix_le R A)
  have hev : ∀ f : Fin (n * n) → R, eval f q = (lovaszMatrix A (f ∘ finProdFinEquiv)).det :=
    fun f => by rw [eval_rename, eval_det_edmondsMatrix]
  have hrp := randProb_blocks_piFinset (n * n) k
    (fun b => (lovaszMatrix A (fun ij => (b (finProdFinEquiv ij) : R))).det ≠ 0)
  -- count the accepted samples as non-zeros of `q` on `S^{n·n}`
  have hcount : #{b ∈ Fintype.piFinset fun _ : Fin (n * n) => range (2 ^ k) |
      (lovaszMatrix A (fun ij => (b (finProdFinEquiv ij) : R))).det ≠ 0}
      = #{f ∈ Fintype.piFinset fun _ : Fin (n * n) => S | eval f q ≠ 0} := by
    refine Finset.card_bij (fun b _ => fun x => (b x : R)) ?_ ?_ ?_
    · intro b hb
      simp only [mem_filter, Fintype.mem_piFinset] at hb ⊢
      exact ⟨fun x => mem_image_of_mem _ (hb.1 x), by rw [hev]; exact hb.2⟩
    · intro b hb b' hb' h
      simp only [mem_filter, Fintype.mem_piFinset] at hb hb'
      funext x
      exact hinj (hb.1 x) (hb'.1 x) (congrFun h x)
    · intro f hf
      simp only [mem_filter, Fintype.mem_piFinset, S, mem_image] at hf
      choose b hb hbf using hf.1
      refine ⟨b, ?_, funext fun x => hbf x⟩
      simp only [mem_filter, Fintype.mem_piFinset]
      refine ⟨hb, ?_⟩
      have hfb : f = fun x => (b x : R) := funext fun x => (hbf x).symm
      subst hfb
      have := hf.2
      rw [hev] at this
      exact this
  have hzero := two_mul_card_eval_eq_zero_le hq S (by omega) (by rw [hS]; positivity)
  have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
    (s := Fintype.piFinset fun _ : Fin (n * n) => S) (p := fun f => eval f q = 0)
  rw [Fintype.card_piFinset_const, hS] at hsplit
  rw [hS] at hzero
  have hpow : (2 ^ k) ^ (n * n) = 2 ^ (n * n * k) := by rw [← pow_mul, mul_comm k]
  have hnat : 2 ^ (n * n * k) ≤ 2 * #{f ∈ Fintype.piFinset fun _ : Fin (n * n) => S |
      eval f q ≠ 0} := by
    simp only [ne_eq] at hsplit ⊢
    omega
  have hrp' : randProb (n * n * k) (fun l => (lovaszMatrix A (lovaszSample R n k l)).det ≠ 0)
      = _ := hrp
  rw [hrp', hcount]
  rw [le_div_iff₀ (by positivity)]
  have : (2 : ℚ) ^ (n * n * k) ≤ 2 * #{f ∈ Fintype.piFinset fun _ : Fin (n * n) => S |
      eval f q ≠ 0} := by exact_mod_cast hnat
  linarith

/-- Only the first `n²k` coins matter. -/
theorem lovaszSample_take (R : Type*) [NatCast R] (n k : ℕ) {m : ℕ} (hm : n * n * k ≤ m)
    (l : List Bool) : lovaszSample R n k (l.take m) = lovaszSample R n k l := by
  funext ij
  have he := (finProdFinEquiv ij).isLt
  have hle : (finProdFinEquiv ij : ℕ) * k + k ≤ m := by
    have : ((finProdFinEquiv ij : ℕ) + 1) * k ≤ n * n * k := Nat.mul_le_mul_right _ he
    nlinarith
  simp only [lovaszSample, blockVal]
  rw [List.drop_take, List.take_take, Nat.min_def, if_pos (by omega)]

/-- **Lovász's test** [AB09, §7.2.4]: if `G` has a perfect matching and each entry of `X` is
replaced by `k` fair coins read as a number below `2^k` (`2n ≤ 2^k`, values distinct in `R`),
then `det ≠ 0` with probability at least `1/2`, for any coin-word length `m ≥ n²k`.

**Proof sketch.** By `randProb_blocks_piFinset` the sample is uniform on `S^{n²}` for
`S = {0, …, 2^k - 1} ⊆ R`. The polynomial `det X` (variables renamed to `Fin (n²)`) is nonzero
of degree `≤ n ≤ |S|/2`, so by Schwartz–Zippel [AB09, Lemma 7.5] at most half of `S^{n²}`
are zeros. Coins after the first `n²k` are ignored (`lovaszSample_take`). -/
theorem lovasz_test {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
    (A : Matrix (Fin n) (Fin n) Bool) (hA : HasPerfectMatching A) {k m : ℕ}
    (hk : 2 * n ≤ 2 ^ k) (hinj : Set.InjOn (Nat.cast : ℕ → R) (range (2 ^ k)))
    (hm : n * n * k ≤ m) :
    1 / 2 ≤ randProb m fun l => (lovaszMatrix A (lovaszSample R n k l)).det ≠ 0 := by
  rw [randProb_congr (B := fun l =>
      (lovaszMatrix A (lovaszSample R n k (l.take (n * n * k)))).det ≠ 0)
    fun r => by beta_reduce; rw [lovaszSample_take R n k le_rfl]]
  exact (lovasz_test_exact A hA hk hinj).trans_eq
    (randProb_take hm (fun l => (lovaszMatrix A (lovaszSample R n k l)).det ≠ 0)).symm

/-- Lovász's test over `ℤ` [AB09, §7.2.4]. -/
theorem lovasz_test_int (A : Matrix (Fin n) (Fin n) Bool) (hA : HasPerfectMatching A)
    {k m : ℕ} (hk : 2 * n ≤ 2 ^ k) (hm : n * n * k ≤ m) :
    1 / 2 ≤ randProb m fun l => (lovaszMatrix A (lovaszSample ℤ n k l)).det ≠ 0 :=
  lovasz_test A hA hk (fun _ _ _ _ h => Int.ofNat_inj.mp h) hm

/-- Lovász's test over `ZMod p` for a prime `p ≥ 2^k ≥ 2n` [AB09, §7.2.4]. -/
theorem lovasz_test_zmod (A : Matrix (Fin n) (Fin n) Bool) (hA : HasPerfectMatching A)
    {p k m : ℕ} [Fact p.Prime] (hk : 2 * n ≤ 2 ^ k) (hkp : 2 ^ k ≤ p) (hm : n * n * k ≤ m) :
    1 / 2 ≤ randProb m fun l => (lovaszMatrix A (lovaszSample (ZMod p) n k l)).det ≠ 0 := by
  refine lovasz_test A hA hk (fun a ha b hb h => ?_) hm
  rw [Finset.coe_range, Set.mem_Iio] at ha hb
  rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
  exact h

/-- One-sided error [AB09, §7.2.4]: without a perfect matching Lovász's test never accepts. -/
theorem randProb_lovasz_eq_zero {R : Type*} [CommRing R] [DecidableEq R]
    (A : Matrix (Fin n) (Fin n) Bool) (hA : ¬ HasPerfectMatching A) (k m : ℕ) :
    randProb m (fun l => (lovaszMatrix A (lovaszSample R n k l)).det ≠ 0) = 0 := by
  rw [randProb_congr (B := fun _ => False) fun r => by simp [det_lovaszMatrix_eq_zero A hA]]
  exact randProb_false

end Randomized.Matching
