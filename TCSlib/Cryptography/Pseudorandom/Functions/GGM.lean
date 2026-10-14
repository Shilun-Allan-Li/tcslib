/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.SubHybrids

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Goldreich–Goldwasser–Micali pseudorandom function

From a length-doubling generator `G(y) = G₀(y) ‖ G₁(y)` the GGM construction
[Gar26, Construction 3.3] defines `F_K(x₁ … x_n) = G_{x_n}(⋯ G_{x₁}(K) ⋯)`: walk down a
binary tree of depth `n` from the root label `K`, taking the left or right half of `G` at
each level according to the input bits. Theorem 3.3 of [Gar26] states that `F` is a
pseudorandom function if `G` is a pseudorandom generator.

This file proves the concrete form: for every oracle adversary `A` making at most `q`
queries,

  `prfAdv F A ≤ ∑_{i < n} ∑_{j < q} distAdv G U (B_{i,j})`,

where `B_{i,j}` (`ggmDist`) is an explicit PRG distinguisher built from `A`, and `U` is
the uniform distribution on pairs of seeds. Hence some `B_{i*,j*}` has advantage at
least `prfAdv F A / (n q)`.

The proof follows [Gar26]. The hybrid `H_i` (`hybridOracle G i`) labels the nodes of
level `i` by a random function `R_i` of the `i`-bit prefix and continues with `G` below
level `i`; `H_0` is `F` and `H_n` is a random function. Between `H_i` and `H_{i+1}` the
oracle is a fixed post-processing (`ggmFrom` from level `i + 1`) of a table indexed by
`i`-bit prefixes, holding `G(R_i(p))` in `H_i` and a uniform pair in `H_{i+1}`; the
sub-hybrid argument of `SubHybrids.lean` applied to the adversary `levelAdv G i A`,
which simulates this post-processing, bounds the gap.

The generator is taken in the form `G : S → S × S` over an arbitrary finite seed type
`S`; `ggmBits` and `ggmBits_prfAdv_le` restate the result for bit strings, with
`G : {0,1}^n → {0,1}^{2n}` split into halves.

## Main definitions

* `ggmFrom G x i y`: apply `G_{x_{i+1}}, …, G_{x_n}` to the label `y` of a level-`i` node.
* `ggm G`: the GGM keyed family `F_K(x) = ggmFrom G x 0 K`.
* `hybridOracle G i`, `hybridProb G A i`: the hybrid `H_i`.
* `levelAdv G i A`: the adversary on level-`i` tables simulating `A`.
* `ggmDist G A q i j`: the PRG distinguisher `B_{i,j}`.
* `ggmBits`: the construction on bit strings.

## Main results

* `hybridProb_zero`, `hybridProb_top`: `H_0 = F` and `H_n = R`.
* `hybridProb_level`: `|H_i - H_{i+1}| ≤ ∑_j distAdv G U B_{i,j}`.
* `ggm_prfAdv_le`, `exists_ggm_dist`: [Gar26, Theorem 3.3], concrete form.
* `ggmBits_prfAdv_le`, `exists_ggmBits_dist`: the same for `G : {0,1}^n → {0,1}^{2n}`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, Construction 3.3 and Theorem 3.3.
-/

namespace TCSlib.Cryptography

open Function QueryTree

attribute [local irreducible] uprob acceptProb

variable {S ρ : Type*} {n : ℕ}

/-- Select the half `G_b` of a generator output: the first component for `b = false`
(the bit `0`) and the second for `b = true`. [Gar26, Construction 3.3]. -/
def pairSel (b : Bool) (v : S × S) : S := if b then v.2 else v.1

/-- The label of the leaf `x` below a node of level `i` with label `y`:
`G_{x_n}(⋯ G_{x_{i+1}}(y) ⋯)`, where the bits are `x 0, …, x (n-1)` (0-indexed).
For `i ≥ n` it is `y`. This is the loop of [Gar26, footnote 4 of §3.4.2] started at
step `i + 1`. -/
def ggmFrom (G : S → S × S) (x : Fin n → Bool) (i : ℕ) (y : S) : S :=
  if h : i < n then ggmFrom G x (i + 1) (pairSel (x ⟨i, h⟩) (G y)) else y
termination_by n - i

/-- Below the last level, one step of the walk applies `G_{x_{i+1}}`. -/
theorem ggmFrom_of_lt (G : S → S × S) (x : Fin n → Bool) {i : ℕ} (h : i < n) (y : S) :
    ggmFrom G x i y = ggmFrom G x (i + 1) (pairSel (x ⟨i, h⟩) (G y)) := by
  rw [ggmFrom, dif_pos h]

/-- At or below the leaves the walk stops: the label is returned unchanged. -/
theorem ggmFrom_of_le (G : S → S × S) (x : Fin n → Bool) {i : ℕ} (h : n ≤ i) (y : S) :
    ggmFrom G x i y = y := by
  rw [ggmFrom, dif_neg (by omega)]

/-- The GGM keyed function family [Gar26, Construction 3.3]: on key `K` and input
`x = x₁ … x_n`, `F_K(x) = G_{x_n}(G_{x_{n-1}}(⋯ G_{x₁}(K) ⋯))`. -/
def ggm (G : S → S × S) : S → (Fin n → Bool) → S := fun K x => ggmFrom G x 0 K

/-- The first `i` bits of `x`, as an `i`-bit string (bits beyond `n` read as `false`;
only `i ≤ n` is used). -/
def prefixAt (x : Fin n → Bool) (i : ℕ) : Fin i → Bool :=
  fun k => if h : k.val < n then x ⟨k, h⟩ else false

/-- The oracle of the hybrid `H_i` [Gar26, proof of Theorem 3.3]: with `R` a function
from `i`-bit prefixes to labels (the random function `K_i`), the input `x` is answered by
`G_{x_n}(⋯ G_{x_{i+1}}(R(x₁ … x_i)) ⋯)`: levels `0, …, i` of the tree are random and the
levels below are pseudorandom. -/
def hybridOracle (G : S → S × S) (i : ℕ) : ((Fin i → Bool) → S) → (Fin n → Bool) → S :=
  fun R x => ggmFrom G x i (R (prefixAt x i))

/-- The probability that `A` accepts in the hybrid `H_i`, with `R` uniform and uniform
coins. [Gar26, proof of Theorem 3.3]. -/
noncomputable def hybridProb [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : ℕ) : ℝ :=
  acceptProb (hybridOracle (n := n) G i) (oracleDist A)

/-- The hybrid `H_0` is the GGM function with a uniform key. [Gar26, proof of
Theorem 3.3, "`H_0` … identical to a pseudorandom function"]. -/
theorem hybridProb_zero [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) :
    hybridProb G A 0 = acceptProb (ggm G) (oracleDist A) := by
  have h : (fun s => hybridOracle G 0 ((Equiv.funUnique (Fin 0 → Bool) S).symm s)) =
      ggm (n := n) G := rfl
  rw [hybridProb, ← h, acceptProb_comp_equiv]

/-- The hybrid `H_n` is a uniform random function. [Gar26, proof of Theorem 3.3,
"`H_n` … identical to … a random function"]. -/
theorem hybridProb_top [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) :
    hybridProb G A n = acceptProb (randomFunction (Fin n → Bool) S) (oracleDist A) := by
  have hp : ∀ x : Fin n → Bool, prefixAt x n = x := fun x => funext fun k => dif_pos k.isLt
  exact acceptProb_congr (fun R => funext fun x => by
    rw [hybridOracle, ggmFrom_of_le G x le_rfl, hp]; rfl) _

/-- The adversary on level-`i` tables that simulates `A`: a query `x` of `A` becomes the
query `x₁ … x_i` to a table of pairs of labels, and the answer pair `v` is turned into
`G_{x_n}(⋯ G_{x_{i+2}}(G_{x_{i+1}}-half of v) ⋯)`. It makes as many queries as `A`. -/
def levelAdv (G : S → S × S) (i : Fin n) (A : OracleAdversary ρ (Fin n → Bool) S) :
    OracleAdversary ρ (Fin i → Bool) (S × S) :=
  fun r => (A r).simulate (fun x => prefixAt x i)
    (fun x v => ggmFrom G x (i + 1) (pairSel (x i) v))

/-- The hybrid `H_i` is the simulated adversary against the table `G ∘ R` of pairs of
pseudorandom labels at level `i + 1`. -/
theorem hybridProb_eq_level_prg [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : Fin n) :
    hybridProb G A i =
      acceptProb (fun R : (Fin i → Bool) → S => G ∘ R) (oracleDist (levelAdv G i A)) := by
  rw [hybridProb, acceptProb, acceptProb]
  refine uprob_congr fun z => iff_of_eq ?_
  simp only [oracleDist, levelAdv, eval_simulate, comp_apply]
  congr 2
  funext x
  rw [hybridOracle, ggmFrom_of_lt G x i.isLt]

/-- The hybrid `H_{i+1}` is the simulated adversary against a uniform table of pairs of
labels at level `i + 1`: a random function on `(i+1)`-bit prefixes is the same as a
random function from `i`-bit prefixes to pairs.

**Proof sketch.** Reparametrize the random function `R_{i+1}` by the bijection that
splits an `(i+1)`-bit prefix into its first `i` bits and its last bit, `R_{i+1}(p b) =`
the `b`-half of `T(p)`; then the `(i+1)`-bit prefix of `x` splits as the `i`-bit prefix
and the bit `x_{i+1}`, which is exactly how the simulated adversary answers. -/
theorem hybridProb_eq_level_random [Fintype S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (i : Fin n) :
    hybridProb G A ((i : ℕ) + 1) =
      acceptProb (randomFunction (Fin i → Bool) (S × S)) (oracleDist (levelAdv G i A)) := by
  let e : ((Fin i → Bool) → S × S) ≃ ((Fin ((i : ℕ) + 1) → Bool) → S) :=
    { toFun := fun T y => pairSel (y (Fin.last i)) (T (Fin.init y))
      invFun := fun R p => (R (Fin.snoc p false), R (Fin.snoc p true))
      left_inv := fun T => funext fun p => by simp [pairSel, Fin.init_snoc]
      right_inv := fun R => funext fun y => by
        change pairSel (y (Fin.last i))
          (R (Fin.snoc (Fin.init y) false), R (Fin.snoc (Fin.init y) true)) = R y
        conv_rhs => rw [← Fin.snoc_init_self y]
        cases y (Fin.last i) <;> rfl }
  have hlast : ∀ x : Fin n → Bool, prefixAt x ((i : ℕ) + 1) (Fin.last i) = x i :=
    fun x => dif_pos i.isLt
  have hinit : ∀ x : Fin n → Bool, Fin.init (prefixAt x ((i : ℕ) + 1)) = prefixAt x i :=
    fun x => rfl
  rw [hybridProb, ← acceptProb_comp_equiv e, acceptProb, acceptProb]
  refine uprob_congr fun z => iff_of_eq ?_
  simp only [oracleDist, levelAdv, eval_simulate, comp_apply, randomFunction, id, e,
    Equiv.coe_fn_mk]
  congr 2
  funext x
  rw [hybridOracle, hlast, hinit]

/-- The PRG distinguisher `B_{i,j}` of [Gar26, proof of Theorem 3.3]. On a challenge
`z = (z₀, z₁) ∈ S × S` it runs `A` once, answering the queries whose `i`-bit prefix is
the `j`-th distinct prefix (0-indexed, in order of first appearance) by
`G_{x_n}(⋯ G_{x_{i+2}}(z_{x_{i+1}}) ⋯)`, earlier prefixes as in `H_{i+1}` and later
prefixes as in `H_i`, and outputs what `A` outputs.

*Cost.* One run of `A`; per query at most `n` evaluations of `G`; `q` fresh seeds and
`q` fresh pairs of seeds as coins together with `A`'s coins, which is lazy sampling of
`R_i` and `R_{i+1}` [Gar26, footnote 9]: no exponential table is sampled; maintaining the
list of at most `q` distinct prefixes. The indices `i, j` are non-uniform advice
[Gar26, footnotes 7 and 8]. -/
noncomputable def ggmDist [Fintype S] [Nonempty S] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) (q : ℕ) (i : Fin n) (j : Fin q) :
    S × S → ((Fin q → S) × (Fin q → S × S)) × ρ → Bool :=
  tableDist G (levelAdv G i A) q j

/-- One level of the hybrid argument: the gap between `H_i` and `H_{i+1}` is at most the
sum over `j < q` of the PRG advantages of `B_{i,j}`. [Gar26, proof of Theorem 3.3,
sub-hybrids `H_{i,j}`].

**Proof sketch.** Write both hybrids as the simulated adversary `levelAdv G i A` against
a table of pseudorandom, respectively uniform, pairs, and apply the sub-hybrid
argument; the simulated adversary makes at most `q` queries. -/
theorem hybridProb_level [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) (i : Fin n) :
    |hybridProb G A i - hybridProb G A ((i : ℕ) + 1)| ≤
      ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  rw [hybridProb_eq_level_prg, hybridProb_eq_level_random]
  exact table_hybrid G (levelAdv G i A) (fun r => (hA r).simulate _ _)

/-- **GGM security** [Gar26, Theorem 3.3], concrete form: for every oracle adversary `A`
making at most `q` queries, the PRF advantage of `A` against the GGM family is at most
the sum, over levels `i < n` and distinct-prefix indices `j < q`, of the PRG
distinguishing advantages of the explicit distinguishers `B_{i,j}` between `G` of a
uniform seed and a uniform pair of seeds.

**Deviation.** The source argues by contradiction and picks `i*, j*` with a large
neighbouring gap; the sum form is the exact quantitative content, and
`exists_ggm_dist` recovers the choice of `i*, j*`. The sub-hybrids are indexed by
distinct prefixes rather than by queries (see `SubHybrids.lean`).

**Proof sketch.** `H_0` is `F` and `H_n` is a random function; telescope over the levels
and bound each level by `hybridProb_level`. -/
theorem ggm_prfAdv_le [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) :
    prfAdv (ggm G) A ≤
      ∑ i : Fin n, ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  rw [prfAdv, distAdv, ← hybridProb_zero, ← hybridProb_top]
  refine (abs_sub_le_sum_hybrids (fun i => hybridProb G A i) n).trans ?_
  rw [Finset.sum_range (fun i => |hybridProb G A i - hybridProb G A (i + 1)|)]
  exact Finset.sum_le_sum fun i _ => hybridProb_level G A hA i

/-- [Gar26, Theorem 3.3], existential form: if `n ≥ 1` and `q ≥ 1`, some distinguisher
`B_{i*,j*}` breaks `G` with advantage at least `prfAdv F A / (n q)`. The indices `i*, j*`
are the non-uniform advice of [Gar26, footnotes 7 and 8].

**Proof sketch.** Otherwise every term of `ggm_prfAdv_le` is below `ε / (n q)` and the
`n q` terms sum to less than `ε`. -/
theorem exists_ggm_dist [Fintype S] [Nonempty S] [Fintype ρ] (G : S → S × S)
    (A : OracleAdversary ρ (Fin n → Bool) S) {q : ℕ} (hA : A.BoundedBy q) (hn : 0 < n)
    (hq : 0 < q) :
    ∃ (i : Fin n) (j : Fin q), prfAdv (ggm G) A / (n * q) ≤
      distAdv G (id : S × S → S × S) (ggmDist G A q i j) := by
  by_contra h
  push_neg at h
  have hsum := ggm_prfAdv_le G A hA
  have hlt : ∑ i : Fin n, ∑ j : Fin q, distAdv G (id : S × S → S × S) (ggmDist G A q i j) <
      ∑ _i : Fin n, ∑ _j : Fin q, prfAdv (ggm G) A / (n * q) := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    have : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ =>
      Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun j _ => h i j
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hval : ∑ _i : Fin n, ∑ _j : Fin q, prfAdv (ggm G) A / (n * q) = prfAdv (ggm G) A := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

/-! ### Bit strings -/

/-- Splitting a `2n`-bit string into its first and last `n` bits, `z = z₀ ‖ z₁`, as a
bijection. With `G` length-doubling, the components of `splitHalves (G y)` are the halves
`G₀(y)` and `G₁(y)` of [Gar26, Construction 3.3]. -/
def splitHalves : (Fin (2 * n) → Bool) ≃ (Fin n → Bool) × (Fin n → Bool) where
  toFun z := (fun k => z ⟨k, by omega⟩, fun k => z ⟨n + k, by omega⟩)
  invFun w k := if h : k.val < n then w.1 ⟨k, h⟩ else w.2 ⟨k - n, by omega⟩
  left_inv z := funext fun k => by
    by_cases h : k.val < n
    · simp [h]
    · simp only [h, dite_false]
      congr 1; ext; simp; omega
  right_inv w := by
    refine Prod.ext (funext fun k => by simp) (funext fun k => ?_)
    simp only
    rw [dif_neg (by simp)]
    exact congrArg w.2 (Fin.ext (by simp))

/-- The GGM construction on bit strings [Gar26, Construction 3.3]: from a length-doubling
`G : {0,1}^n → {0,1}^{2n}`, the keyed family `F_K(x) = G_{x_n}(⋯ G_{x₁}(K) ⋯)` on
`n`-bit keys, inputs and outputs, with `G₀, G₁` the first and last `n` bits of `G`. -/
def ggmBits (G : (Fin n → Bool) → Fin (2 * n) → Bool) :
    (Fin n → Bool) → (Fin n → Bool) → Fin n → Bool :=
  ggm (splitHalves ∘ G)

/-- The PRG distinguisher `B_{i,j}` for a length-doubling `G` on bit strings: split the
`2n`-bit challenge into halves and run `ggmDist`. Same cost as `ggmDist`. -/
noncomputable def ggmBitsDist (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) (q : ℕ) (i : Fin n) (j : Fin q) :
    (Fin (2 * n) → Bool) →
      ((Fin q → Fin n → Bool) × (Fin q → (Fin n → Bool) × (Fin n → Bool))) × ρ → Bool :=
  fun z c => ggmDist (splitHalves ∘ G) A q i j (splitHalves z) c

/-- The advantage of `ggmBitsDist` against `G` with a uniform `2n`-bit string is the
advantage of `ggmDist` against the split generator with a uniform pair. -/
theorem distAdv_ggmBitsDist [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) (q : ℕ) (i : Fin n) (j : Fin q) :
    distAdv G (id : (Fin (2 * n) → Bool) → _) (ggmBitsDist G A q i j) =
      distAdv (splitHalves ∘ G) id (ggmDist (splitHalves ∘ G) A q i j) := by
  have h : acceptProb (id : (Fin (2 * n) → Bool) → _) (ggmBitsDist G A q i j) =
      acceptProb (id : (Fin n → Bool) × (Fin n → Bool) → _)
        (ggmDist (splitHalves ∘ G) A q i j) := by
    refine Eq.trans ?_ (acceptProb_comp_equiv splitHalves id _)
    rw [acceptProb, acceptProb]; rfl
  have h' : acceptProb G (ggmBitsDist G A q i j) =
      acceptProb (splitHalves ∘ G) (ggmDist (splitHalves ∘ G) A q i j) := by
    rw [acceptProb, acceptProb]; rfl
  rw [distAdv, distAdv, h, h']

/-- **GGM security for bit strings** [Gar26, Theorem 3.3], concrete form: for a
length-doubling `G : {0,1}^n → {0,1}^{2n}` and every oracle adversary making at most `q`
queries, the PRF advantage against `ggmBits G` is at most the sum over `i < n`, `j < q` of
the PRG advantages of `ggmBitsDist G A q i j` (between `G(U_n)` and `U_{2n}`). -/
theorem ggmBits_prfAdv_le [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q) :
    prfAdv (ggmBits G) A ≤
      ∑ i : Fin n, ∑ j : Fin q, distAdv G id (ggmBitsDist G A q i j) := by
  simp only [distAdv_ggmBitsDist]
  exact ggm_prfAdv_le _ A hA

/-- [Gar26, Theorem 3.3] for bit strings, existential form: if `n, q ≥ 1`, some
`B_{i*,j*}` distinguishes `G(U_n)` from `U_{2n}` with advantage at least
`prfAdv F A / (n q)`. -/
theorem exists_ggmBits_dist [Fintype ρ] (G : (Fin n → Bool) → Fin (2 * n) → Bool)
    (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q)
    (hn : 0 < n) (hq : 0 < q) :
    ∃ (i : Fin n) (j : Fin q),
      prfAdv (ggmBits G) A / (n * q) ≤ distAdv G id (ggmBitsDist G A q i j) := by
  simp only [distAdv_ggmBitsDist]
  have : Nonempty (Fin n → Bool) := ⟨fun _ => false⟩
  exact exists_ggm_dist _ A hA hn hq

end TCSlib.Cryptography
