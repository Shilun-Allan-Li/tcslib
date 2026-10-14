/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling
import TCSlib.Cryptography.Pseudorandom.Functions.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sub-hybrids: a table of PRG outputs against an adaptive adversary

This file isolates the inner hybrid argument of the GGM proof [Gar26, proof of
Theorem 3.3, "Sub-hybrids"]. Let `G : S → V` be a generator and consider an oracle
adversary `A` making at most `q` queries to a table `T : P → V`. In the *pseudorandom*
world the table is `G ∘ R` for a uniform `R : P → S`; in the *random* world it is a
uniform `T : P → V`. We bound the gap by `q` PRG distinguishing advantages.

The sub-hybrid `H_j` (`subHybridProb G A q j`) answers the queries lazily: the `k`-th
distinct query is answered by a uniform value of `V` if `k < j` and by `G` of a uniform
seed otherwise. So `H_0` is the pseudorandom world and `H_q` the random world, by lazy
sampling (`QueryTree.uprob_evalLazy`). The PRG distinguisher `tableDist G A q j` embeds
its challenge `z ∈ V` as the answer to the `j`-th distinct query; it accepts with the
probability of `H_j` when `z = G(s)` and with that of `H_{j+1}` when `z` is uniform.

**Deviation from the source.** [Gar26] defines `H_{i,j}` through a list `L` of prefixes,
which amounts to answering the first `j` *distinct* prefixes randomly, as here. The
argument then speaks of "the `(j*+1)`-th query", claims that it cannot repeat an earlier
prefix "because otherwise the hybrids would be identical" (not a valid inference: two
hybrids can differ although they agree on a particular event), and has the outer
adversary answer only that one query with its challenge, which leaves later queries with
the same prefix inconsistent with the challenge. Here the sub-hybrids are indexed by
distinct queries in order of first appearance, and the distinguisher answers *every*
query equal to the `j`-th distinct one with the challenge. A repeated query is then
simply answered by its recorded value, so no case split on repeats is needed, and the
distinguisher's runs coincide pointwise with those of the hybrids after relabelling one
uniform coordinate.

## Main definitions

* `subHybridStream G j W`, `subHybridProb G A q j`: the sub-hybrid `H_j`.
* `tableDist G A q j`: the PRG distinguisher embedding its challenge at the `j`-th
  distinct query.

## Main results

* `acceptProb_tableDist_prg`, `acceptProb_tableDist_uniform`: the distinguisher realises
  `H_j` and `H_{j+1}`.
* `subHybridProb_zero`, `subHybridProb_top`: the endpoints are the pseudorandom and the
  random table.
* `table_hybrid`: the gap between the two worlds is at most the sum over `j < q` of the
  distinguishing advantages of `tableDist G A q j`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4.2, proof of Theorem 3.3 (sub-hybrids `H_{i,j}` and the
  outer adversary `B`), footnote 9 (lazy sampling).
-/

namespace TCSlib.Cryptography

open Function QueryTree

attribute [local irreducible] uprob acceptProb

variable {P S V ρ : Type*} [Fintype P] [DecidableEq P] [Fintype S] [Nonempty S]
  [Fintype V] [Nonempty V] [Fintype ρ]

/-- The answer stream of the sub-hybrid `H_j` [Gar26, proof of Theorem 3.3]: the `k`-th
distinct query is answered by the uniform value `W.2 k` if `k < j` and by the generator
output `G (W.1 k)` on a uniform seed otherwise. -/
noncomputable def subHybridStream {q : ℕ} (G : S → V) (j : ℕ)
    (W : (Fin q → S) × (Fin q → V)) : ℕ → V :=
  fun k => if k < j then extendStream W.2 k else G (extendStream W.1 k)

/-- The oracle adversary `A` run with lazily sampled answers given by an answer stream. -/
def lazyDist (A : OracleAdversary ρ P V) : (ℕ → V) → ρ → Bool :=
  fun a r => (A r).evalLazy a []

/-- The probability that `A` accepts in the sub-hybrid `H_j`: `j` uniform values and
`q - j` generator outputs answer the distinct queries in order. [Gar26, proof of
Theorem 3.3, `H_{i,j}`] with the level `i` abstracted away; see the module docstring for
the indexing by distinct queries. -/
noncomputable def subHybridProb (G : S → V) (A : OracleAdversary ρ P V) (q j : ℕ) : ℝ :=
  acceptProb (subHybridStream (q := q) G j) (lazyDist A)

/-- The answer stream of the PRG distinguisher: as in `H_j`, except that the `j`-th
distinct query is answered by the challenge `z`. -/
noncomputable def challengeStream {q : ℕ} (G : S → V) (j : ℕ) (z : V)
    (W : (Fin q → S) × (Fin q → V)) : ℕ → V :=
  fun k => if k < j then extendStream W.2 k else if k = j then z else G (extendStream W.1 k)

/-- The PRG distinguisher built from the oracle adversary `A` [Gar26, proof of
Theorem 3.3, the outer adversary `B`]. On a challenge `z ∈ V` and coins
`((W₀, W₁), r)` with `W₀ : Fin q → S`, `W₁ : Fin q → V`, it runs `A` once on coins `r`,
answers the `k`-th distinct query by `W₁ k` if `k < j`, by `z` if `k = j`, and by
`G (W₀ k)` if `k > j`, and outputs what `A` outputs.

*Cost.* One run of `A`; at most `q` evaluations of `G`; `q` seeds and `q` values of
fresh randomness (lazy sampling, [Gar26, footnote 9]: no exponential table is sampled);
bookkeeping of the list of at most `q` distinct queries (membership and position
lookups). -/
noncomputable def tableDist (G : S → V) (A : OracleAdversary ρ P V) (q j : ℕ) :
    V → ((Fin q → S) × (Fin q → V)) × ρ → Bool :=
  fun z c => (A c.2).evalLazy (challengeStream G j z c.1) []

omit [Fintype P] in
/-- On a pseudorandom challenge `z = G s` the distinguisher `tableDist G A q j` accepts
exactly with the probability of the sub-hybrid `H_j`, for `j < q`.

**Proof sketch.** With `z = G s`, the challenge stream is the stream of `H_j` with the
seed table `W₀` overwritten at position `j` by `s`; overwriting one entry of a uniform
table by a uniform value leaves it uniform. -/
theorem acceptProb_tableDist_prg (G : S → V) (A : OracleAdversary ρ P V) {q j : ℕ}
    (hj : j < q) : acceptProb G (tableDist G A q j) = subHybridProb G A q j := by
  have hs : ∀ (s : S) (W : (Fin q → S) × (Fin q → V)),
      challengeStream G j (G s) W = subHybridStream G j (update W.1 ⟨j, hj⟩ s, W.2) := by
    intro s W; funext k
    unfold challengeStream subHybridStream
    by_cases h1 : k < j
    · simp [h1]
    · by_cases h2 : k = j
      · subst h2; simp only [lt_irrefl, if_false, if_true]
        exact congrArg G (extendStream_update_self W.1 ⟨k, hj⟩ s).symm
      · rw [if_neg h1, if_neg h1, if_neg h2, extendStream_update_of_ne _ _ _ h2]
  let E : (Fin q → S) → (Fin q → V) × ρ → Prop :=
    fun W₀ c => (A c.2).evalLazy (subHybridStream G j (W₀, c.1)) [] = true
  let e : S × ((Fin q → S) × ((Fin q → V) × ρ)) ≃ S × (((Fin q → S) × (Fin q → V)) × ρ) :=
    (Equiv.refl S).prodCongr (Equiv.prodAssoc _ _ _).symm
  have h1 : acceptProb G (tableDist G A q j) =
      uprob (fun z : S × ((Fin q → S) × ((Fin q → V) × ρ)) =>
        E (update z.2.1 ⟨j, hj⟩ z.1) z.2.2) := by
    rw [acceptProb, ← uprob_comp_equiv e
      (fun z : S × (((Fin q → S) × (Fin q → V)) × ρ) => tableDist G A q j (G z.1) z.2 = true)]
    exact uprob_congr fun z => iff_of_eq
      (congrArg (fun a => (A z.2.2.2).evalLazy a [] = true) (hs z.1 (z.2.1, z.2.2.1)))
  have h2 : subHybridProb G A q j = uprob (fun z : (Fin q → S) × ((Fin q → V) × ρ) => E z.1 z.2) := by
    rw [subHybridProb, acceptProb, ← uprob_comp_equiv (Equiv.prodAssoc _ _ _).symm
      (fun z : ((Fin q → S) × (Fin q → V)) × ρ => lazyDist A (subHybridStream G j z.1) z.2 = true)]
    rfl
  rw [h1, h2]
  exact uprob_update_absorb _ E

omit [Fintype P] in
/-- On a uniform challenge `z` the distinguisher `tableDist G A q j` accepts exactly
with the probability of the sub-hybrid `H_{j+1}`, for `j < q`.

**Proof sketch.** With `z` uniform, the challenge stream is the stream of `H_{j+1}` with
the uniform value table `W₁` overwritten at position `j` by `z`, which is again
uniform. -/
theorem acceptProb_tableDist_uniform (G : S → V) (A : OracleAdversary ρ P V) {q j : ℕ}
    (hj : j < q) :
    acceptProb (id : V → V) (tableDist G A q j) = subHybridProb G A q (j + 1) := by
  have hs : ∀ (z : V) (W : (Fin q → S) × (Fin q → V)),
      challengeStream G j z W = subHybridStream G (j + 1) (W.1, update W.2 ⟨j, hj⟩ z) := by
    intro z W; funext k
    unfold challengeStream subHybridStream
    by_cases h1 : k < j
    · rw [if_pos h1, if_pos (by omega), extendStream_update_of_ne _ _ _ (by simp; omega)]
    · by_cases h2 : k = j
      · subst h2; simp only [lt_irrefl, Nat.lt_succ_self, if_false, if_true]
        exact (extendStream_update_self W.2 ⟨k, hj⟩ z).symm
      · rw [if_neg h1, if_neg h2, if_neg (by omega)]
  let E : (Fin q → V) → (Fin q → S) × ρ → Prop :=
    fun W₁ c => (A c.2).evalLazy (subHybridStream G (j + 1) (c.1, W₁)) [] = true
  let e : V × ((Fin q → V) × ((Fin q → S) × ρ)) ≃ V × (((Fin q → S) × (Fin q → V)) × ρ) :=
    (Equiv.refl V).prodCongr
      { toFun := fun c => ((c.2.1, c.1), c.2.2)
        invFun := fun c => (c.1.2, (c.1.1, c.2))
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  let e' : (Fin q → V) × ((Fin q → S) × ρ) ≃ ((Fin q → S) × (Fin q → V)) × ρ :=
    { toFun := fun c => ((c.2.1, c.1), c.2.2)
      invFun := fun c => (c.1.2, (c.1.1, c.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h1 : acceptProb (id : V → V) (tableDist G A q j) =
      uprob (fun z : V × ((Fin q → V) × ((Fin q → S) × ρ)) =>
        E (update z.2.1 ⟨j, hj⟩ z.1) z.2.2) := by
    rw [acceptProb, ← uprob_comp_equiv e
      (fun z : V × (((Fin q → S) × (Fin q → V)) × ρ) => tableDist G A q j (id z.1) z.2 = true)]
    exact uprob_congr fun z => iff_of_eq
      (congrArg (fun a => (A z.2.2.2).evalLazy a [] = true) (hs z.1 (z.2.2.1, z.2.1)))
  have h2 : subHybridProb G A q (j + 1) =
      uprob (fun z : (Fin q → V) × ((Fin q → S) × ρ) => E z.1 z.2) := by
    rw [subHybridProb, acceptProb, ← uprob_comp_equiv e'
      (fun z : ((Fin q → S) × (Fin q → V)) × ρ =>
        lazyDist A (subHybridStream G (j + 1) z.1) z.2 = true)]
    rfl
  rw [h1, h2]
  exact uprob_update_absorb _ E

/-- The sub-hybrid `H_0` is the pseudorandom table: for an adversary making at most `q`
queries, answering every distinct query by `G` of a fresh seed is the same as querying
`G ∘ R` for a uniform `R : P → S`. [Gar26, proof of Theorem 3.3, "`H_{i,0}` is the same
as `H_i`"].

**Proof sketch.** Condition on the adversary's coins; post-compose the tree's answers
with `G` and apply lazy sampling for seeds. -/
theorem subHybridProb_zero (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ}
    (hA : A.BoundedBy q) :
    subHybridProb G A q 0 = acceptProb (fun R : P → S => G ∘ R) (oracleDist A) := by
  have h1 : subHybridProb G A q 0 = uprob (fun z : ρ × ((Fin q → S) × (Fin q → V)) =>
      ((A z.1).simulate id (fun _ => G)).evalLazy (extendStream z.2.1) [] = true) := by
    rw [subHybridProb, acceptProb]
    refine (uprob_prod_comm (fun W r => lazyDist A (subHybridStream G 0 W) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    have hs : subHybridStream G 0 z.2 = G ∘ extendStream z.2.1 := by
      funext k; simp [subHybridStream]
    rw [lazyDist, hs, evalLazy_comp]
  have h2 : acceptProb (fun R : P → S => G ∘ R) (oracleDist A) =
      uprob (fun z : ρ × (P → S) => ((A z.1).simulate id (fun _ => G)).eval z.2 = true) := by
    rw [acceptProb]
    refine (uprob_prod_comm (fun R r => oracleDist A (G ∘ R) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    rw [eval_simulate]; rfl
  rw [h1, h2]
  refine uprob_sections_congr
    (fun r (W : (Fin q → S) × (Fin q → V)) =>
      ((A r).simulate id (fun _ => G)).evalLazy (extendStream W.1) [] = true)
    (fun r (R : P → S) => ((A r).simulate id (fun _ => G)).eval R = true) fun r => ?_
  exact (uprob_fst (fun W : Fin q → S =>
    ((A r).simulate id (fun _ => G)).evalLazy (extendStream W) [] = true)).trans
    (uprob_evalLazy (· = true) ((hA r).simulate _ _))

/-- The sub-hybrid `H_q` is the random table: for an adversary making at most `q`
queries, all its distinct queries are answered by fresh uniform values, which is the same
as querying a uniform random function `P → V`. [Gar26, proof of Theorem 3.3, "`H_{i,q}`
is the same as `H_{i+1}`"].

**Proof sketch.** The adversary never reaches a `q`-th distinct query, so the stream of
`H_q` may be replaced by the uniform values alone; then condition on the coins and apply
lazy sampling. -/
theorem subHybridProb_top (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ}
    (hA : A.BoundedBy q) :
    subHybridProb G A q q = acceptProb (randomFunction P V) (oracleDist A) := by
  have h1 : subHybridProb G A q q = uprob (fun z : ρ × ((Fin q → S) × (Fin q → V)) =>
      (A z.1).evalLazy (extendStream z.2.2) [] = true) := by
    rw [subHybridProb, acceptProb]
    refine (uprob_prod_comm (fun W r => lazyDist A (subHybridStream G q W) r = true)).trans
      (uprob_congr fun z => iff_of_eq ?_)
    rw [lazyDist]
    congr 1
    exact evalLazy_congr (hA z.1) [] fun k hk => if_pos (by simpa using hk)
  have h2 : acceptProb (randomFunction P V) (oracleDist A) =
      uprob (fun z : ρ × (P → V) => (A z.1).eval z.2 = true) := by
    rw [acceptProb]
    exact uprob_prod_comm (fun T r => oracleDist A (randomFunction P V T) r = true)
  rw [h1, h2]
  refine uprob_sections_congr
    (fun r (W : (Fin q → S) × (Fin q → V)) => (A r).evalLazy (extendStream W.2) [] = true)
    (fun r (T : P → V) => (A r).eval T = true) fun r => ?_
  exact (uprob_snd (fun W : Fin q → V => (A r).evalLazy (extendStream W) [] = true)).trans
    (uprob_evalLazy (· = true) (hA r))

/-- **Sub-hybrid argument.** For an adversary making at most `q` queries to a table, the
gap between the pseudorandom table `G ∘ R` and a uniform table is at most the sum over
`j < q` of the PRG distinguishing advantages of `tableDist G A q j`, with `G` of a
uniform seed against a uniform element of `V`. [Gar26, proof of Theorem 3.3, sub-hybrids
`H_{i,0}, …, H_{i,q}` at one level], an exact inequality.

**Proof sketch.** The endpoints are `H_0` and `H_q`; telescope, and identify each
neighbouring gap `|H_j - H_{j+1}|` with the advantage of `tableDist G A q j`. -/
theorem table_hybrid (G : S → V) (A : OracleAdversary ρ P V) {q : ℕ} (hA : A.BoundedBy q) :
    |acceptProb (fun R : P → S => G ∘ R) (oracleDist A) -
        acceptProb (randomFunction P V) (oracleDist A)| ≤
      ∑ j : Fin q, distAdv G (id : V → V) (tableDist G A q j) := by
  rw [← subHybridProb_zero G A hA, ← subHybridProb_top G A hA]
  have key := abs_sub_le_sum_hybrids (fun j => subHybridProb G A q j) q
  have hsum : ∑ i ∈ Finset.range q, |subHybridProb G A q i - subHybridProb G A q (i + 1)| =
      ∑ j : Fin q, distAdv G (id : V → V) (tableDist G A q j) := by
    rw [Finset.sum_range (fun j => |subHybridProb G A q j - subHybridProb G A q (j + 1)|)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 := acceptProb_tableDist_prg G A j.isLt
    have h2 := acceptProb_tableDist_uniform G A j.isLt
    unfold distAdv
    rw [h1, h2]
  exact key.trans hsum.le

end TCSlib.Cryptography
