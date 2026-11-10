/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.GGMReduction
import TCSlib.Cryptography.Asymptotic.GGMReductionEval
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Asymptotic.PRFLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.GGM
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Stretch
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The asymptotic Goldreich–Goldwasser–Micali construction

The GGM tree of [PS10, Theorem 97.3] builds a pseudorandom function from a
length-doubling generator. The oracle and PRF contracts live in
`Pseudorandom.Functions.Asymptotic.Defs` and are available through this import.
`Pseudorandom.Generators.Asymptotic.Stretch` reduces an arbitrary secure PRG to
the length-doubling case.

The evaluator uses `Asymptotic.PRFLemmas`. The reduction machine and its run
agreement are in `Asymptotic.GGMReduction` and `Asymptotic.GGMReductionEval`.
The finite level and query hybrids come from [Gar26, Theorem 3.3].

**Deviation.** The level hybrids are indexed `HF⁰ = f_s, …, HFⁿ = RF_n` with
`n` gaps. The query sub-hybrids are indexed by distinct prefixes in order of
first appearance.

## Main definitions

* `TCSlib.Cryptography.ggmPRF` is the GGM family `f_s(b₁ … b_n) = g_{b_n}(⋯ g_{b₁}(s) ⋯)`.

## Main results

* `TCSlib.Cryptography.exists_ggmPRF_evaluator` computes the GGM family in polynomial time.
* `TCSlib.Cryptography.thm_97_3_1` and `thm_97_3_2` give the level hybrids and query
  sub-hybrid bound. `exists_ggmBitsDist_nuppt` implements the reduction as a machine.
* `TCSlib.Cryptography.ggmPRF_prf` proves security, and `exists_prf_of_exists_prg`
  composes it with PRG stretch extension.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8, Theorem 97.3.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4, Construction 3.3 and Theorem 3.3.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### The GGM construction [PS10, Theorem 97.3] -/

/-- **The GGM family** [PS10, Theorem 97.3, construction] (Constr-97.b): for a length-doubling
generator `g(x) = g₀(x) ‖ g₁(x)`, `f_s(b₁ b₂ … b_n) = g_{b_n}(g_{b_{n−1}}(⋯ (g_{b₁}(s)) ⋯))` —
a walk down a binary tree of height `n` whose root is the seed `s` and whose children of a
node `y` are `g₀(y)` and `g₁(y)`. This is the concrete `ggmBits (G n)` [Gar26, Construction 3.3]
at every parameter. -/
def ggmPRF (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) :
    ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool) :=
  fun n => ggmBits (G n)

/-- Unfolding: the GGM family at `n` is `ggmBits (G n)`. -/
@[simp] theorem ggmPRF_apply (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) (n : ℕ) :
    ggmPRF G n = ggmBits (G n) := rfl

/-- **The GGM evaluation is polynomial-time** (Claim-97.c, clause (1) of
[PS10, Definition 96.2] for the GGM family): from a polynomial-time evaluator `E` of the
length-doubling generator, a polynomial-time string function computes `f_s(x)` from `⟨s, x⟩`.

**Proof sketch.** `n` iterations of "evaluate `E` on the current label and keep the half
selected by the next bit of `x`": `Complexity.polyTimeComputable_iterate` with `R := var`
(at most `|⟨s, x⟩|` rounds) on the state word `⟨y, rest⟩` (current label `y`, remaining bits
`rest` of `x`), whose step is `⟨pairSel (head rest) (E y), tail rest⟩` with `pairSel b` the
first or last `|y|` bits (`polyTimeComputable_pairTakePoly`/`pairDropPoly` at `var` on
`⟨1^{|y|}, E y⟩`, `polyTimeComputable_unaryPoly`, `polyTimeComputable_ite` on the head bit,
`Turing.FinTM.computesFunInTime_stripLast`-style head/tail primitives); the orbit is bounded by
`|⟨s, x⟩| + 2` since labels keep length `n`; the output is the label after `|x|` rounds (the
step is the identity once `rest = []`). The functional identity with `ggmBits (G n) s x =
ggmFrom (splitHalves ∘ G n) x 0 s` is proved by induction on the position `i`
(`ggmFrom_of_lt`, `ggmFrom_of_le`, `splitHalves` as take/drop of `ofFn`). -/
theorem exists_ggmPRF_evaluator {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hG : ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)) :
    ∃ E' : List Bool → List Bool, PolyTimeComputable E' ∧
      ∀ n (s x : Fin n → Bool), E' (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (ggmPRF G n s x) :=
  ⟨ggmEval E, ggmEval_poly hE, fun n s x => ggmEval_ofFn (hG n) s x⟩

/-- **The level hybrids** `HF^i` of [PS10, proof of Theorem 97.3] (Thm-97.3.1): with levels
`0, …, i` of the tree random and the levels below pseudorandom (`hybridOracle`), the hybrid
`HF⁰` is the GGM function with a uniform seed and `HFⁿ` is a uniform random function `RF_n`
(`hybridProb_zero`, `hybridProb_top`).

**Deviation:** the formal indexing is `HF⁰ = f_s, …, HFⁿ = RF_n` (`n` gaps) where the text
writes `HF¹ = f_s, …, HFⁿ = RF_n`. -/
theorem thm_97_3_1 {ρ : Type*} [Fintype ρ] (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool))
    (n : ℕ) (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) :
    hybridProb (splitHalves ∘ G n) A 0 = acceptProb (ggmPRF G n) (oracleDist A) ∧
      hybridProb (splitHalves ∘ G n) A n =
        acceptProb ((OracleEnsemble.random .var .var).O n) (oracleDist A) :=
  ⟨by rw [ggmPRF_apply, ggmBits_def]; exact hybridProb_zero _ A, by
    rw [OracleEnsemble.acceptProb_random_eq]
    exact hybridProb_top _ A⟩

/-- **The query sub-hybrids** `HHF^j` of [PS10, proof of Theorem 97.3] (Thm-97.3.2): for an
adversary making at most `q` queries, the gap between the consecutive level hybrids `HF^i` and
`HF^{i+1}` is at most the sum over `j < q` of the PRG advantages of the explicit distinguishers
`B_{i,j} = ggmBitsDist (G n) A q i j` between `G(U_n)` and `U_{2n}` (`hybridProb_level`,
`distAdv_ggmBitsDist`). Together with `exists_ggmBits_dist` this is the text's "`D` can
distinguish `HHF^j` and `HHF^{j+1}` for some `j` with probability `ε/(n p(n))`".

**Deviation:** the sub-hybrids are indexed by *distinct* prefixes in order of first
appearance, the challenge answering every query with the `j`-th distinct prefix. -/
theorem thm_97_3_2 {ρ : Type*} [Fintype ρ] (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool))
    (n : ℕ) (A : OracleAdversary ρ (Fin n → Bool) (Fin n → Bool)) {q : ℕ} (hA : A.BoundedBy q)
    (i : Fin n) :
    |hybridProb (splitHalves ∘ G n) A i - hybridProb (splitHalves ∘ G n) A ((i : ℕ) + 1)| ≤
      ∑ j : Fin q, prgAdv (G n) (ggmBitsDist (G n) A q i j) := by
  have h := hybridProb_level (splitHalves ∘ G n) A hA i
  simpa only [prgAdv_eq, distAdv_ggmBitsDist] using h

/-- The history encoding is `TCSlib.Cryptography.GGMRed.histEnc`:
`encodeHist h = GGMRed.histEnc h`. -/
theorem encodeHist_eq_histEnc {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist h = GGMRed.histEnc h := by
  rw [GGMRed.histEnc_eq]
  induction h with
  | nil => exact encodeHist_nil
  | cons p h ih => rw [encodeHist_cons, ih, List.foldr_cons]

/-- `decodeOracleMove` in terms of the `Option` form of `TCSlib.Cryptography.GGMRed`: the
query `queryOf` if there is one, else the verdict `verdictOf` (`[true, true]` is the only
accepting output).

**Proof sketch.** Along the published case readers of `decodeOracleMove`: a pair `⟨[false], x⟩`
decodes as `decodeFin ℓ₁ x` decides (`decodeOracleMove_pairEncode_false`), which is
`queryOf` (`GGMRed.queryOf_eq`), and its failure is `ret false = verdictOf` of a word starting
with `false`; the two-bit word `[true, b]` decodes to `ret b` (`decodeOracleMove_true_two`),
which is `verdictOf [true, b]`, and is no query; any other word is neither a query nor
`[true, true]` (`decodeOracleMove_of_ne`, `GGMRed.queryOf_eq_some_iff`). -/
private theorem decodeOracleMove_eq (ℓ₁ : ℕ) (w : List Bool) :
    decodeOracleMove ℓ₁ w =
      match GGMRed.queryOf ℓ₁ w with
      | some x => .query x
      | none => .ret (GGMRed.verdictOf w) := by
  by_cases hq : ∃ x, w = pairEncode [false] x
  · obtain ⟨x, rfl⟩ := hq
    have hqo : GGMRed.queryOf ℓ₁ (pairEncode [false] x) = decodeFin ℓ₁ x := by
      rw [GGMRed.queryOf_eq, pairDecode_pairEncode]
    rw [hqo, decodeOracleMove_pairEncode_false]
    cases decodeFin ℓ₁ x with
    | some y => rfl
    | none =>
      show OracleMove.ret false = OracleMove.ret (GGMRed.verdictOf (pairEncode [false] x))
      rw [GGMRed.verdictOf_eq, decide_eq_false (by simp [pairEncode_eq])]
  · by_cases hv : ∃ b, w = [true, b]
    · obtain ⟨b, rfl⟩ := hv
      have hqn : GGMRed.queryOf ℓ₁ [true, b] = none := by
        rw [GGMRed.queryOf_eq, pairDecode_true_two]
      rw [hqn, decodeOracleMove_true_two, GGMRed.verdictOf_eq]
      cases b <;> rfl
    · push_neg at hq hv
      have hqn : GGMRed.queryOf ℓ₁ w = none := by
        rw [Option.eq_none_iff_forall_ne_some]
        intro x hx
        rw [GGMRed.queryOf_eq_some_iff] at hx
        exact hq (List.ofFn x) (eq_pairEncode_of_pairDecode w _ _ hx)
      rw [hqn, decodeOracleMove_of_ne ℓ₁ hq hv]
      simp only [OracleMove.ret.injEq, GGMRed.verdictOf_eq]
      exact (decide_eq_false_iff_not.2 fun h => hv true h).symm

/-- `buildTree` of the decoded moves is `buildTreeQ` of the raw outputs.

**Proof sketch.** Induct on the budget. A verdict stops both trees. A query with
budget zero rejects in both. With budget remaining, both query the same string and
their continuations agree by the induction hypothesis. -/
private theorem buildTree_eq_buildTreeQ {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool) :
    ∀ (b : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      buildTree (fun h => decodeOracleMove ℓ₁ (next h)) b hist = GGMRed.buildTreeQ next b hist
  | 0, hist => by
    rw [GGMRed.buildTreeQ_zero]
    have hmove := decodeOracleMove_eq ℓ₁ (next hist)
    cases h : GGMRed.queryOf ℓ₁ (next hist) with
    | none =>
      rw [h] at hmove
      exact buildTree_zero_of_ret hmove
    | some x =>
      rw [h] at hmove
      exact buildTree_zero_of_query hmove
  | b + 1, hist => by
    rw [GGMRed.buildTreeQ_succ]
    have hmove := decodeOracleMove_eq ℓ₁ (next hist)
    cases h : GGMRed.queryOf ℓ₁ (next hist) with
    | none =>
      rw [h] at hmove
      exact buildTree_succ_of_ret hmove
    | some x =>
      rw [h] at hmove
      rw [buildTree_succ_of_query (next := fun h => decodeOracleMove ℓ₁ (next h)) (hist := hist) hmove]
      simp only
      congr 1
      funext o
      exact buildTree_eq_buildTreeQ next b (hist ++ [(x, o)])

/-- **A sub-hybrid can be emulated by a non-uniform PPT** (Thm-97.3.3, [PS10, proof of
Theorem 97.3, last paragraph]: "queries to `HHF^j` can be emulated in p.p.t. … it follows by
closure under efficient operations that `D` contradicts the pseudorandom property of `g`"):
for a next-query machine `D` with budget `q` and hybrid indices `i, j : ℕ → ℕ` (the
non-uniform advice of the reduction), there is a non-uniform PPT `B` whose PRG advantage
against `G n` is exactly the advantage of the concrete distinguisher
`ggmBitsDist (G n) (D^{(q n)}) (q n) (i n) (j n)` whenever the indices are in range.

**Proof sketch.** `B` has advice `⟨⟨1^{i n}, 1^{j n}⟩, D.advice n⟩` (`NUPPT.exists_withAdvice`
with bound `.add (.add (.mul (.const 2) .var) (.const 2)) q`-style) and coins
`(q · n) + (q · 2n) + D.coins` (`NUPPT.exists_split` twice: the `q n` fresh seeds and the `q n`
fresh pairs of the lazily sampled tables `R_i`, `R_{i+1}`, read as blocks by
`polyTimeComputable_blockMap`). On the challenge `z ∈ {0,1}^{2n}` it hosts `D`'s next-query
function in a `Complexity.polyTimeComputable_iterateFind` loop over at most `q n + 1`
activations: the state word holds the encoded history, the list of distinct `i`-bit prefixes
seen so far (`QueryTree.noteQuery`), and `D`'s single random tape; each round runs `D.output` on
the history (`NUPPT.polyTimeComputable_output`), decodes the move (`decodeOracleMove`:
`pairDecode`/`decodeFin` are FP), and answers a query `x` by walking the lower part of the tree
from the label of its prefix — the `k`-th distinct prefix gets the uniform pair `W₁ k` if
`k < j n`, the challenge `splitHalves z` if `k = j n`, and `G(W₀ k)` otherwise
(`challengeStream`), then `n − i − 1` evaluations of `E` with half selection
(`exists_ggmPRF_evaluator`'s loop); `acc` is "the move is a verdict", `out` the verdict bit.
The functional identity `B.distinguisher n (2n) z r = ggmBitsDist (G n) (D^{(q n)}) … z (c r)`
is proved by induction on the query tree (`buildTree`, `QueryTree.evalLazy`, `levelAdv`,
`tableDist`), and the coin reindexing `c` is a bijection
`Fin (B.coinLen n) → Bool ≃ ((Fin q → Fin n → Bool) × (Fin q → (Fin n → Bool) × (Fin n → Bool))) × D.Coins n`
(`FunFamily.blocks`, `Fin.appendEquiv`, `splitHalves`), so `acceptProb_comp_equiv` gives the
equality of advantages. -/
theorem exists_ggmBitsDist_nuppt {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (hG : ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)) (D : NUPPT)
    (q : PolyExpr) (i j : ℕ → ℕ) :
    ∃ B : NUPPT, ∀ n (hi : i n < n) (hj : j n < q.eval n),
      prgAdv (G n) (B.distinguisher n (2 * n)) =
        prgAdv (G n) (ggmBitsDist (G n) (D.toOracleAdversary n n n (q.eval n)) (q.eval n)
          ⟨i n, hi⟩ ⟨j n, hj⟩) := by
  refine ⟨GGMRed.ggmRedMachine hE D q i j, fun n hi hj => ?_⟩
  have hA : D.toOracleAdversary n n n (q.eval n) = fun r =>
      GGMRed.buildTreeQ (fun hist => D.runAt n (GGMRed.histEnc hist) r) (q.eval n) [] := by
    funext r
    rw [NUPPT.toOracleAdversary_eq]
    simp only [encodeHist_eq_histEnc]
    exact buildTree_eq_buildTreeQ _ (q.eval n) []
  rw [hA]
  let e₁ : (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool)) ≃ (Fin (q.eval n * (2 * n)) → Bool) :=
    (Equiv.piCongrRight fun _ => splitHalves.symm).trans (FunFamily.blocks (q.eval n) (2 * n)).symm
  let e : ((Fin (q.eval n) → Fin n → Bool) × (Fin (q.eval n) → (Fin n → Bool) × (Fin n → Bool))) ×
      D.Coins n ≃ (GGMRed.ggmRedMachine hE D q i j).Coins n :=
    (Equiv.prodAssoc _ _ _).trans
      (((FunFamily.blocks (q.eval n) n).symm.prodCongr
        ((e₁.prodCongr (Equiv.refl (D.Coins n))).trans
          (Fin.appendEquiv (q.eval n * (2 * n)) (D.coinLen n)))).trans
        ((Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)).trans
          (GGMRed.ggmRedMachine_coinsEquiv hE D q i j n).symm))
  refine prgAdv_coins_equiv (G n) _ _ e fun z c => ?_
  obtain ⟨⟨W₁, W₂⟩, r⟩ := c
  refine GGMRed.ggmRedMachine_distinguisher hE D q i j (G n) (hG n) hi hj z (W₁, W₂) r
    (e ((W₁, W₂), r)) ?_
  show List.ofFn ((GGMRed.ggmRedMachine_coinsEquiv hE D q i j n).symm
    (Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)
      ((FunFamily.blocks (q.eval n) n).symm W₁,
        Fin.appendEquiv (q.eval n * (2 * n)) (D.coinLen n) (e₁ W₂, r)))) = _
  rw [← GGMRed.ggmRedMachine_coinsEquiv_ofFn hE D q i j n, Equiv.apply_symm_apply,
    ofFn_appendEquiv, ofFn_appendEquiv, GGMRed.coinStr_eq]
  rfl

/-- **A next-query machine with query budget `0` has PRF advantage `0`:** with budget `0` the
tree `buildTree … 0 []` is a leaf whose verdict depends on the coins only, so both acceptance
probabilities are the same average over the coins (`uprob_snd`). -/
private theorem prfAdv_toOracleAdversary_zero
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) (D : NUPPT) (n : ℕ) :
    prfAdv (F n) (D.toOracleAdversary n n n 0) = 0 := by
  have hA : ∀ r, ∃ b : Bool, D.toOracleAdversary n n n 0 r = .ret b := by
    intro r
    rw [NUPPT.toOracleAdversary_eq]
    cases h : decodeOracleMove n (D.runAt n (encodeHist []) r) with
    | ret b => exact ⟨b, buildTree_zero_of_ret h⟩
    | query x => exact ⟨false, buildTree_zero_of_query h⟩
  choose b hb using hA
  have key : ∀ {σ : Type} [Fintype σ] [Nonempty σ] (X : σ → (Fin n → Bool) → (Fin n → Bool)),
      uprob (fun z : σ × D.Coins n => (D.toOracleAdversary n n n 0 z.2).eval (X z.1) = true) =
        uprob fun r : D.Coins n => b r = true := by
    intro σ _ _ X
    rw [← uprob_snd (α := σ) (fun r : D.Coins n => b r = true)]
    refine uprob_congr fun z => ?_
    rw [hb z.2, QueryTree.eval_ret]
  rw [prfAdv_eq, key (F n), key (fun R => R), sub_self, abs_zero]

/-- **[PS10, Theorem 97.3] (Goldreich–Goldwasser–Micali): the GGM family of a length-doubling
pseudorandom generator is a pseudorandom function.**

**Proof sketch.** *Easy:* `exists_ggmPRF_evaluator` from `hG.easy`. *Pseudorandom:* fix a
next-query machine `D` and a budget `q` using `OracleEnsemble.indist_iff`. We show
`μ n := prfAdv (ggmPRF G n) (D^{(q n)})` is negligible (`prfAdv_toOracleAdversary`). Suppose not; by `not_negligible_iff` there is `c` with
`μ n > 1/n^c` for infinitely many `n`. *Concrete step* (Thm-97.3.1, Thm-97.3.2): at every `n` with
`0 < n` and `0 < q n`, `exists_ggmBits_dist (G n) (D^{(q n)}) (toOracleAdversary_boundedBy …)`
gives indices `(i n, j n)` with `μ n / (n · q n) ≤ prgAdv (G n) (ggmBitsDist … (i n) (j n))`
(choose them by `Classical.choose`; put `(0, 0)` elsewhere). *Machine step* (Thm-97.3.3):
`exists_ggmBitsDist_nuppt hE hG D q i j` yields one non-uniform PPT `B` with
`prgAdv (G n) (B.distinguisher n (2n)) = prgAdv (G n) (ggmBitsDist … (i n) (j n))` at those `n`.
*Asymptotic step:* `hG.negligible_prgAdv B` says `ν n := prgAdv (G n) (B.distinguisher n (2n))`
is negligible, hence so is `n · q n · ν n` (`Negligible.mul_pow` with `q n ≤ C (n+1)^d` from
`PolyExpr.eval_le`, `Negligible.const_mul`, `Negligible.mono`), while `μ n ≤ n · q n · ν n`
infinitely often contradicts `μ n > 1/n^c` (`not_negligible_iff`). At parameters with
`q n = 0` the adversary makes no query and `μ n = 0` (`buildTree` with budget `0` is a leaf
whose verdict does not depend on the oracle, `distAdv` of a constant distinguisher is `0`). -/
theorem ggmPRF_prf {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)} (hG : DoublingPRG G) :
    PRF (ggmPRF G) := by
  obtain ⟨E, hE, hGE⟩ := hG.easy
  refine ⟨exists_ggmPRF_evaluator hE hGE, ?_⟩
  rw [OracleEnsemble.indist_iff]
  intro D q
  suffices hμ : Negligible fun n => prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) from
    (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary (ggmPRF G) D n (q.eval n))).mpr hμ
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  have hidx : ∀ n, 0 < n → 0 < q.eval n → ∃ (i : Fin n) (j : Fin (q.eval n)),
      prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) / (n * q.eval n) ≤
        prgAdv (G n) (ggmBitsDist (G n) (D.toOracleAdversary n n n (q.eval n)) (q.eval n) i j) :=
    fun n hn hq => by
      simpa only [ggmPRF_apply, prgAdv_eq] using
        exists_ggmBits_dist (G n) _ (D.toOracleAdversary_boundedBy n n n (q.eval n)) hn hq
  classical
  let i : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then (Classical.choose (hidx n h.1 h.2)).val else 0
  let j : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then
      (Classical.choose (Classical.choose_spec (hidx n h.1 h.2))).val else 0
  obtain ⟨B, hB⟩ := exists_ggmBitsDist_nuppt hE hGE D q i j
  obtain ⟨n₀, hn₀⟩ := (negligible_iff _).1 ((hG.negligible_prgAdv B).polyExpr_mul (.mul .var q)) c
  obtain ⟨n, hn, hμn⟩ := hc (max n₀ 1)
  have hn1 : 0 < n := le_of_max_le_right hn
  have hpos : (0 : ℝ) < 1 / (n : ℝ) ^ c := by
    have : (0 : ℝ) < n := by exact_mod_cast hn1
    positivity
  by_cases hq : 0 < q.eval n
  · have hgood : 0 < n ∧ 0 < q.eval n := ⟨hn1, hq⟩
    have hin : i n = (Classical.choose (hidx n hn1 hq)).val := by simp [i, hgood]
    have hjn : j n = (Classical.choose (Classical.choose_spec (hidx n hn1 hq))).val := by
      simp [j, hgood]
    have hi : i n < n := hin ▸ (Classical.choose (hidx n hn1 hq)).isLt
    have hj : j n < q.eval n :=
      hjn ▸ (Classical.choose (Classical.choose_spec (hidx n hn1 hq))).isLt
    have hspec := Classical.choose_spec (Classical.choose_spec (hidx n hn1 hq))
    have hBn := hB n hi hj
    have hfin : (⟨i n, hi⟩ : Fin n) = Classical.choose (hidx n hn1 hq) := Fin.ext hin
    have hfin' : (⟨j n, hj⟩ : Fin (q.eval n)) =
        Classical.choose (Classical.choose_spec (hidx n hn1 hq)) := Fin.ext hjn
    rw [hfin, hfin'] at hBn
    rw [← hBn] at hspec
    have hbound := hn₀ n (le_of_max_le_left hn)
    simp only [PolyExpr.eval_mul, PolyExpr.eval_var, Nat.cast_mul] at hbound
    have hnq : (0 : ℝ) < (n : ℝ) * (q.eval n : ℝ) := by
      have h1 : (0 : ℝ) < n := by exact_mod_cast hn1
      have h2 : (0 : ℝ) < q.eval n := by exact_mod_cast hq
      positivity
    rw [div_le_iff₀ hnq] at hspec
    have h0 : 0 ≤ prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) := prfAdv_nonneg _ _
    rw [abs_of_nonneg h0] at hμn
    have h3 := le_abs_self ((n : ℝ) * (q.eval n : ℝ) * prgAdv (G n) (B.distinguisher n (2 * n)))
    linarith
  · have hq0 : q.eval n = 0 := Nat.eq_zero_of_not_pos hq
    rw [hq0, prfAdv_toOracleAdversary_zero, abs_zero] at hμn
    linarith

/-- **[PS10, Theorem 97.3], as stated: if a pseudorandom generator exists, then pseudorandom
functions exist.** From a secure `PRG` build the length-doubling generator `P.doubling`
(Cor-97.a, `PRG.Secure.doubling`) and take its GGM family (`ggmPRF_prf`). -/
theorem exists_prf_of_exists_prg (h : ∃ P : PRG, P.Secure) :
    ∃ F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool), PRF F :=
  let ⟨P, hP⟩ := h
  ⟨ggmPRF P.doubling, ggmPRF_prf hP.doubling⟩

end TCSlib.Cryptography
