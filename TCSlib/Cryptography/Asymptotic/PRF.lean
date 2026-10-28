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

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle indistinguishability, pseudorandom functions and the GGM construction

The material of [PS10, §3.8]: random functions `RF_n` in their two descriptions (the function
table and the lazily sampled machine, §3.8.1); oracle indistinguishability of ensembles of
distributions over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` against non-uniform PPT oracle
machines [PS10, Definition 96.1]; pseudorandom functions [PS10, Definition 96.2]; and the
Goldreich–Goldwasser–Micali theorem that a pseudorandom generator yields a pseudorandom
function [PS10, Theorem 97.3] through the tree construction
`f_s(b₁ … b_n) = g_{b_n}(⋯ g_{b₁}(s) ⋯)`.

Two layers (foundation decision D2 of `PassShelatChapter2-4Plan.md`). The *concrete* layer is
the frozen Garg development reused verbatim: query trees and oracle adversaries
(`Pseudorandom/Functions/OracleAdversary.lean`), lazy sampling (`LazySampling.lean`), random
functions and the PRF advantage `prfAdv` (`Defs.lean`), the level hybrids, the query
sub-hybrids and the GGM security bound `exists_ggmBits_dist` (`SubHybrids.lean`, `GGM.lean`).
The *asymptotic* layer is the oracle-adversary model of foundation decision D7: an oracle
machine is a *next-query* `Complexity.NUPPT`, activated once per query on the encoded history
of (query, answer) pairs with one random tape per parameter, with an explicit query budget
quantified universally; `Complexity.NUPPT.toOracleAdversary` unfolds it into a concrete
`OracleAdversary` making at most `q` queries. The theorems are (i) the concrete reduction at
each `n`, (ii) a machine built by the closure calculus of `TCSlib/Complexity/Randomized/`,
(iii) negligible-function arithmetic.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries.

**Deviation:** the GGM tree of [PS10, Theorem 97.3] is built from a *length-doubling*
generator `G : {0,1}^n → {0,1}^{2n}`, which the text obtains "without loss of generality"; a
length-doubling generator is not a `PRG` of this library (the stretch `2n` does not exceed `n`
at `n = 0`), so it is the separate predicate `DoublingPRG`, and the reduction from an arbitrary
`PRG` is the explicit `PRG.doubling` (truncate to `n + 1` bits, expand by [PS10, Lemma 80.5] to
`2n + 1` bits, truncate to `2n`).

**Deviation:** the level hybrids of the formal proof are indexed `HF⁰ = f_s, …, HFⁿ = RF_n`
(`n` gaps, loss `1/n`) where the text writes `HF¹ = f_s, …, HFⁿ = RF_n`; the query sub-hybrids
are indexed by distinct prefixes in order of first appearance (`SubHybrids.lean`).

Proof infrastructure lives in three sibling files: `TCSlib.Cryptography.Asymptotic.PRFLemmas`
(truncation of a generator, the GGM evaluator `ggmEval`), and
`TCSlib.Cryptography.Asymptotic.GGMReduction` / `GGMReductionEval` (the reduction machine
`GGMRed.ggmRedMachine` of Thm-97.3.3: a state loop hosting `D`'s next-query function with the
lazily sampled tables, and its functional identity with `ggmBitsDist`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` — an ensemble of distributions over functions
  [PS10, Definition 96.1]; `OracleEnsemble.random` — the random functions `RF_n`
  [PS10, §3.8.1]; `OracleEnsemble.keyed` — `{s ← U_n : f_s}`.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, `encodeHist`, `buildTree`,
  `Complexity.NUPPT.toOracleAdversary` — next-query machines as oracle adversaries (D7).
* `TCSlib.Cryptography.OracleEnsemble.Indist` — oracle indistinguishability
  [PS10, Definition 96.1].
* `TCSlib.Cryptography.PRF` — pseudorandom function families [PS10, Definition 96.2].
* `TCSlib.Cryptography.DoublingPRG`, `PRG.truncate`, `PRG.doubling` — length-doubling
  generators and the reduction from an arbitrary generator (Cor-97.a).
* `TCSlib.Cryptography.ggmPRF` — the GGM family `f_s(b₁ … b_n) = g_{b_n}(⋯ g_{b₁}(s) ⋯)`
  [PS10, Theorem 97.3, construction].

## Main results

* `Complexity.NUPPT.toOracleAdversary_boundedBy` — the unfolded tree makes at most `q` queries.
* `TCSlib.Cryptography.acceptProb_random_eq_lazy` — the table and the lazy descriptions of a
  random function give the same acceptance probabilities (Claim-95.b).
* `TCSlib.Cryptography.OracleEnsemble.Indist.refl`, `.symm`, `.trans`,
  `TCSlib.Cryptography.oracle_hybrid_lemma` — reflexivity, symmetry, transitivity and the
  hybrid lemma for oracle ensembles (Claim-96.b).
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` — the advantage of a next-query machine
  against a keyed family is the concrete `prfAdv`.
* `TCSlib.Cryptography.PRG.Secure.doubling` — every PRG yields a length-doubling PRG
  (Cor-97.a).
* `TCSlib.Cryptography.thm_97_3_1`, `thm_97_3_2`, `exists_ggmBitsDist_nuppt` — the level
  hybrids, the query sub-hybrids and the emulation of a sub-hybrid by a non-uniform PPT.
* `TCSlib.Cryptography.ggmPRF_prf` — the GGM family of a length-doubling PRG is a PRF
  [PS10, Theorem 97.3]; `exists_prf_of_exists_prg` — "if a PRG exists then a PRF exists".

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.8: Definitions 96.1, 96.2; Theorem 97.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9, Construction 3.3, Theorem 3.3).
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Oracle ensembles and random functions [PS10, §3.8.1, Definition 96.1] -/

/-- An **oracle ensemble** [PS10, Definition 96.1]: for every parameter `n` a probability
distribution over functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, given (D6/D7) as the pushforward
of the uniform distribution on a finite seed type `σ n` along a sampler `O n`. For the
random-function ensemble the seed is the function table itself (exponentially long, which is
immaterial at the concrete level); for a keyed family the seed is the key.

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where
  /-- The seed type at parameter `n`. -/
  σ : ℕ → Type
  /-- The seed types are finite. -/
  [fintype : ∀ n, Fintype (σ n)]
  /-- The sampler: the oracle determined by a seed. -/
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)

attribute [instance] OracleEnsemble.fintype

/-- **The random function ensemble** `RF_n` [PS10, §3.8.1, combinatorial description]: the
uniform distribution on functions `{0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}`, sampled by its function
table (the "long array" of the text; `randomFunction I O = id`). The text's count
`2^{n 2^n}` of random functions is `Fintype.card_fun`. -/
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂ where
  σ n := (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
  O _ := randomFunction _ _

/-- **A keyed family as an oracle ensemble**: `{s ← U_n : f_s}` for a family
`F n : {0,1}^n → {0,1}^{ℓ₁(n)} → {0,1}^{ℓ₂(n)}` (the first clause of the pseudorandomness
condition of [PS10, Definition 96.2]); the seed is the `n`-bit key. -/
def OracleEnsemble.keyed {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    OracleEnsemble ℓ₁ ℓ₂ where
  σ n := Fin n → Bool
  O n := F n

/-- Unfolding: the random-function ensemble samples by the identity on tables. -/
@[simp] theorem OracleEnsemble.random_O (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (R : (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) :
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R := rfl

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- **The two descriptions of a random function agree** [PS10, §3.8.1, "both of the above
descriptions of a random function give rise to identical distributions"] (Claim-95.b): for an
oracle adversary making at most `q` queries, the probability of accepting with the function
table `RF_n` as oracle equals the probability of accepting when every *new* query is answered
by a fresh uniform value and repeated queries by the recorded answer (the computational
description, `QueryTree.evalLazy` with `q` fresh values `extendStream W`).

**Proof sketch.** Both sides are averages over the adversary's coins `r` (Fubini,
`uprob_prod` after swapping the factors with `uprob_prod_comm`); for each fixed `r` the two
inner probabilities agree by the concrete lazy-sampling theorem `QueryTree.uprob_evalLazy`
applied to the tree `A r`. -/
theorem acceptProb_random_eq_lazy {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) {q : ℕ}
    (hA : A.BoundedBy q) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (fun W : Fin q → (Fin (ℓ₂.eval n) → Bool) => extendStream W) (lazyDist A) := by
  show uprob (fun z : ((Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
      (A z.2).eval z.1 = true) =
    uprob (fun z : (Fin q → (Fin (ℓ₂.eval n) → Bool)) × ρ =>
      (A z.2).evalLazy (extendStream z.1) [] = true)
  rw [uprob_prod_comm (fun R (r : ρ) => (A r).eval R = true),
    uprob_prod_comm (fun W (r : ρ) => (A r).evalLazy (extendStream W) [] = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  exact (QueryTree.uprob_evalLazy (· = true) (hA r)).symm

/-! ### Next-query machines as oracle adversaries (D7) -/

/-- A move of a next-query oracle machine: either the next query `x ∈ {0,1}^{ℓ₁}` or the
final verdict `b`. -/
inductive OracleMove (ℓ₁ : ℕ)
  /-- Ask the oracle at `x`. -/
  | query (x : Fin ℓ₁ → Bool)
  /-- Stop with the verdict `b`. -/
  | ret (b : Bool)

/-- Decoding of a machine output as a move: `⟨[false], x⟩` with `x` an `ℓ₁`-bit string is the
query `x`; the two-bit string `[true, b]` is the verdict `b`; any other output is the verdict
`false` (D7: ill-formed outputs count as rejection). -/
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁ :=
  match pairDecode w, w with
  | some ([false], x), _ => match decodeFin ℓ₁ x with
    | some x => .query x
    | none => .ret false
  | _, [true, b] => .ret b
  | _, _ => .ret false

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The query tree of a next-query function `next` (the machine's move on a history) with the
query budget `q`, started from the history `hist`: a verdict stops; a query within budget
becomes a `query` node whose continuation appends the answer to the history; a query when the
budget is exhausted is the forced verdict `false` (D7). -/
def buildTree {ℓ₁ ℓ₂ : ℕ} (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ℕ → List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
  | 0, hist => match next hist with
    | .ret b => .ret b
    | .query _ => .ret false
  | q + 1, hist => match next hist with
    | .ret b => .ret b
    | .query x => .query x (fun o => buildTree next q (hist ++ [(x, o)]))

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    unfold buildTree
    cases next hist <;> exact trivial
  | q + 1, hist => by
    unfold buildTree
    cases next hist with
    | ret b => exact trivial
    | query x => exact fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  fun _ => buildTree_boundedBy _ q []

/-! ### Oracle indistinguishability [PS10, Definition 96.1] -/

/-- **Oracle indistinguishability** [PS10, Definition 96.1]: `{O_n} ≈ {O'_n}` iff for every
non-uniform PPT oracle machine `D` (a next-query `NUPPT`) and every polynomial query budget
`q`, the function `n ↦ |Pr[F ← O_n : D^F(1^n) = 1] − Pr[F ← O'_n : D^F(1^n) = 1]|` is
negligible, where `D^F(1^n)` is the run of the query tree `D.toOracleAdversary n ℓ₁(n) ℓ₂(n) q(n)`
against `F`. (The text writes `{O'_n} ≈ {O'_n}`, a typo.)

**Deviation:** `OracleEnsemble.Indist`: next-query machines with an explicit universally
quantified budget; no oracle tapes; forced verdict `false` after `q n` queries. -/
def OracleEnsemble.Indist {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
    distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv]
  rw [h]
  exact negligible_zero

/-- **Symmetry of oracle indistinguishability**: the advantage is symmetric in the two
ensembles (`abs_sub_comm`). -/
theorem OracleEnsemble.Indist.symm {ℓ₁ ℓ₂ : PolyExpr} {O O' : OracleEnsemble ℓ₁ ℓ₂}
    (h : O.Indist O') : O'.Indist O := by
  intro D q
  have e : (fun n => distAdv (O'.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) =
      fun n => distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := by
    funext n
    exact abs_sub_comm _ _
  rw [e]
  exact h D q

/-- **Transitivity of oracle indistinguishability** (the two-step case of the hybrid lemma
for oracles, [PS10, §3.8.2, "oracle indistinguishability satisfies … the Hybrid Lemma"]): the
advantage between `O` and `O''` is at most the sum of the advantages between `O, O'` and
`O', O''` (triangle inequality `abs_sub_le`), and sums of negligible functions are negligible
(`Negligible.add`, `Negligible.mono`). -/
theorem OracleEnsemble.Indist.trans {ℓ₁ ℓ₂ : PolyExpr} {O O' O'' : OracleEnsemble ℓ₁ ℓ₂}
    (h₁ : O.Indist O') (h₂ : O'.Indist O'') : O.Indist O'' := by
  intro D q
  refine ((h₁ D q).add (h₂ D q)).mono ⟨0, fun n _ => ?_⟩
  have t := abs_sub_le (acceptProb (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
    (acceptProb (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
    (acceptProb (O''.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))))
  have h0 : 0 ≤ distAdv (O.O n) (O'.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) +
      distAdv (O'.O n) (O''.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  have h1 : 0 ≤ distAdv (O.O n) (O''.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) := abs_nonneg _
  rw [abs_of_nonneg h1, abs_of_nonneg h0]
  exact t

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. This is the
concrete `hybrid_lemma` (`exists_hybrid_gap`) applied to the distinguisher `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ I O ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) :=
  hybrid_lemma hm H (oracleDist A)

/-! ### Pseudorandom functions [PS10, Definition 96.2] -/

/-- **Pseudorandom function family** [PS10, Definition 96.2]: a family
`{f_s : {0,1}^{|s|} → {0,1}^{|s|}}` given as `F n : {0,1}^n → {0,1}^n → {0,1}^n` (key, input,
output) is pseudorandom iff (1) *easy to compute*: a polynomial-time string function computes
`f_s(x)` from the pair `⟨s, x⟩`; (2) *pseudorandom*: the keyed oracle ensemble `{s ← U_n : f_s}`
is oracle-indistinguishable from the random functions `{F ← RF_n : F}`.

**Deviation:** clause (1) is a deterministic polynomial-time evaluator on `⟨s, x⟩` instead of
a PPT computing `f_s(x)` with probability one (equivalent by `Complexity.NUPPT.Computes` and
`ofPolyTimeUniform`, as for `FunFamily.Easy`); the key length is the parameter `n`
(`{0,1}^{|s|}` with `|s| = n`). -/
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where
  /-- Clause (1): `f_s(x)` is polynomial-time computable from `⟨s, x⟩`. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  /-- Clause (2): `{s ← U_n : f_s} ≈ {F ← RF_n : F}` as oracle ensembles. -/
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)

/-- The advantage of the next-query machine `D` with budget `q` between the keyed family `F`
and the random functions is the concrete PRF advantage `prfAdv` of [Gar26, Definition 3.9]
(definitional: `prfAdv F A = distAdv F (randomFunction I O) (oracleDist A)`). -/
theorem prfAdv_toOracleAdversary (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
    (D : NUPPT) (n q : ℕ) :
    distAdv ((OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).O n) ((OracleEnsemble.random .var .var).O n)
        (oracleDist (D.toOracleAdversary n n n q)) =
      prfAdv (F n) (D.toOracleAdversary n n n q) := rfl

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) := by
  have h := hF.pseudorandom D q
  simpa only [prfAdv_toOracleAdversary] using h

/-! ### Length-doubling generators (Cor-97.a) -/

/-- The output ensemble `{s ← U_n : G(s)}` of a length-doubling generator
`G : {0,1}^n → {0,1}^{2n}`, with the stretch `2n` as the syntactic polynomial `2 · var` (D9). -/
def doublingEnsemble (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) :
    Ensemble (.mul (.const 2) .var) where
  σ n := Fin n → Bool
  X := G

/-- **A length-doubling pseudorandom generator** `g : {0,1}^n → {0,1}^{2n}` [PS10, proof of
Theorem 97.3, "let `g` be a length-doubling pseudorandom generator"]: efficiently computable
and with a pseudorandom output ensemble, exactly as `PRG.Secure` [PS10, Definition 77.1] but
with the stretch `2n`.

**Deviation:** a length-doubling generator is not a `PRG` of this library (the expansion
clause `n < 2n` fails at `n = 0`), hence this separate predicate; `PRG.Secure.doubling`
(Cor-97.a) produces one from any `PRG`. -/
structure DoublingPRG (G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)) : Prop where
  /-- Efficiency: a polynomial-time string function computes `G n s` from the seed string. -/
  easy : ∃ E : List Bool → List Bool, PolyTimeComputable E ∧
    ∀ n (s : Fin n → Bool), E (List.ofFn s) = List.ofFn (G n s)
  /-- Pseudorandomness of the output ensemble [PS10, Definition 74.1]. -/
  pseudorandom : (doublingEnsemble G).Pseudorandom

/-- **Pseudorandomness of a length-doubling generator unfolded**: for every non-uniform PPT
`D` the concrete PRG advantage `prgAdv (G n) (D(1^n, ·))` [Gar26, Definition 3.5] between
`G(U_n)` and `U_{2n}` is negligible (definitional, `Ensemble.pseudorandom_iff_prgAdv`). -/
theorem DoublingPRG.negligible_prgAdv {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)}
    (hG : DoublingPRG G) (D : NUPPT) :
    Negligible fun n => prgAdv (G n) (D.distinguisher n (2 * n)) :=
  (Ensemble.pseudorandom_iff_prgAdv (doublingEnsemble G)).1 hG.pseudorandom D

/-- **Truncation of a generator to `n + 1` bits** (first step of Cor-97.a): the first `n + 1`
output bits of `G n` (the stretch `ℓ(n) > n` makes them available). -/
def PRG.truncate (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool) :=
  fun n s i => P.G n s (Fin.castLE (P.expands n) i)

/-- The stretch `2n + 1` used to produce a length-doubling generator from a one-bit-stretch
generator by [PS10, Lemma 80.5]: it exceeds `n` at every `n` (unlike `2n`). -/
theorem two_mul_add_one_expands (n : ℕ) :
    n < (PolyExpr.add (.mul (.const 2) .var) (.const 1)).eval n := by
  show n < 2 * n + 1
  omega

/-- **The length-doubling generator obtained from an arbitrary PRG** (Cor-97.a, the "without
loss of generality" of [PS10, proof of Theorem 97.3]): truncate `G` to `n + 1` bits
(`PRG.truncate`), expand the one-bit-stretch generator to `2n + 1` bits by the construction of
[PS10, Lemma 80.5] (`PRG.expand`), and keep the first `2n` bits. -/
def PRG.doubling (P : PRG) : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool) :=
  fun n s i => (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
    two_mul_add_one_expands).G n s (Fin.castLE (Nat.le_succ (2 * n)) i)

/-- Closed form of the length-doubling generator: bit `i` of `P.doubling n s` is the last bit
of the truncated generator applied to the `i`-th iterate of `s ↦ init (G₁(s))` on `s`
(`PRG.expand_G`). -/
theorem PRG.doubling_apply (P : PRG) (n : ℕ) (s : Fin n → Bool) (i : Fin (2 * n)) :
    P.doubling n s i =
      P.truncate n ((fun x => Fin.init (P.truncate n x))^[i] s) (Fin.last n) := rfl

/-- **Truncation preserves pseudorandomness** (first half of Cor-97.a): if `G` is a secure
PRG then its truncation to `n + 1` bits is a secure one-bit-stretch PRG.

**Proof sketch.** *Easy:* the evaluator of `G` followed by `List.take (n + 1)`
(`Complexity.polyTimeComputable_pairTakePoly (.add .var (.const 1))` on `⟨1^n, G(s)⟩`, with
`1^n = replicate |s| true` by `polyTimeComputable_unaryPoly .var`); `List.take` of `ofFn` is
`ofFn` of the restriction (`List.ofFn_castLE`-style, `List.take_ofFn`). *Pseudorandom:* for a
distinguisher `D` of the truncation, the machine `D'` that truncates its `ℓ(n)`-bit input to
`n + 1` bits and runs `D` (`NUPPT.exists_comp` with `pre := pairTakePoly`) satisfies
`prgAdv (G n) (D'.distinguisher n (ℓ n)) = prgAdv (P.truncate n) (D.distinguisher n (n+1))` by
the sunglass identity `distAdv_comp` with the projection `t ↦ t ∘ castLE` (a uniform
`ℓ(n)`-bit string projects to a uniform `(n+1)`-bit string, `uprob_comp_equiv` on
`Fin.appendEquiv`/`Equiv.funSplitAt`), and `PRG.secure_iff` applied to `hP` gives the
negligible bound; `Negligible.mono` with the equality. -/
theorem PRG.Secure.truncate {P : PRG} (hP : P.Secure) : (PRG.oneBit P.truncate).Secure := by
  have hm : ∀ n, (PolyExpr.add .var (.const 1)).eval n ≤ P.stretch.eval n := fun n => P.expands n
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hP.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hP.truncateTo_negligible _ hm D

/-- **Any PRG yields a length-doubling PRG** (Cor-97.a, [PS10, proof of Theorem 97.3, first
paragraph]): if `G` is a secure PRG then `P.doubling : {0,1}^n → {0,1}^{2n}` is a secure
length-doubling generator.

**Proof sketch.** By `PRG.Secure.truncate` the one-bit-stretch generator `P.truncate` is
secure, so by [PS10, Lemma 80.5] (`prg_expand` with `ℓ := 2 · var + 1`) the expansion to
`2n + 1` bits is a secure `PRG`; `P.doubling` is its truncation to `2n` bits
(`PRG.doubling_apply`, `PRG.expand_G`). *Easy:* the evaluator of the expansion followed by
`List.take (2n)` (`polyTimeComputable_pairTakePoly (.mul (.const 2) .var)`). *Pseudorandom:*
exactly as in `PRG.Secure.truncate`: a distinguisher `D` of `P.doubling` becomes the
distinguisher `D ∘ take (2n)` of the expansion (`NUPPT.exists_comp`), `distAdv_comp` with the
projection `Fin (2n + 1) → Fin (2n)` and `uprob_comp_equiv` identify the advantages, and the
pseudorandomness of the expansion (`PRG.secure_iff`) gives the negligible bound. -/
theorem PRG.Secure.doubling {P : PRG} (hP : P.Secure) : DoublingPRG P.doubling := by
  have hQ : (PRG.expand P.truncate (.add (.mul (.const 2) .var) (.const 1))
      two_mul_add_one_expands).Secure :=
    prg_expand P.truncate _ two_mul_add_one_expands hP.truncate
  have hm : ∀ n, (PolyExpr.mul (.const 2) .var).eval n ≤
      (PolyExpr.add (.mul (.const 2) .var) (.const 1)).eval n := fun n => Nat.le_succ _
  refine ⟨?_, fun D => ?_⟩
  · obtain ⟨E, hE, hEs⟩ := hQ.truncateTo_easy _ hm
    exact ⟨E, hE, fun n s => hEs n s⟩
  · exact hQ.truncateTo_negligible _ hm D

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
  ⟨hybridProb_zero _ A, hybridProb_top _ A⟩

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
  simpa only [prgAdv, distAdv_ggmBitsDist] using h

/-- `decodeOracleMove` in terms of the `Option` form of `TCSlib.Cryptography.GGMRed`: the
query `queryOf` if there is one, else the verdict `verdictOf` (`[true, true]` is the only
accepting output).

**Proof sketch.** Case split along the match of `decodeOracleMove`. A pair `⟨[false], x⟩`
decodes to the query `x` iff `|x| = ℓ₁`, and otherwise to `ret false`, which is `verdictOf` of
a word starting with `false`. The two-bit word `[true, b]` is not a pair and decodes to `ret b`,
which is `verdictOf [true, b]`. Any other word is neither a query nor `[true, true]`. -/
private theorem decodeOracleMove_eq (ℓ₁ : ℕ) (w : List Bool) :
    decodeOracleMove ℓ₁ w =
      match GGMRed.queryOf ℓ₁ w with
      | some x => .query x
      | none => .ret (GGMRed.verdictOf w) := by
  unfold decodeOracleMove
  split
  · rename_i w o w' x hx
    have hw := eq_pairEncode_of_pairDecode w _ _ hx
    have hq : GGMRed.queryOf ℓ₁ w = decodeFin ℓ₁ x := by
      simp only [GGMRed.queryOf, hx]
    rw [hq]
    cases decodeFin ℓ₁ x with
    | some y => rfl
    | none =>
      simp only
      congr 1
      rw [hw]
      simp [GGMRed.verdictOf, pairEncode]
  · rename_i o w' b hp
    have hq : GGMRed.queryOf ℓ₁ [true, b] = none := by cases b <;> rfl
    rw [hq]
    cases b <;> rfl
  · rename_i w o w' hb hp
    have hq : GGMRed.queryOf ℓ₁ w = none := by
      rw [Option.eq_none_iff_forall_ne_some]
      intro x hx
      rw [GGMRed.queryOf_eq_some_iff] at hx
      exact hp (List.ofFn x) hx
    rw [hq]
    simp only [OracleMove.ret.injEq, GGMRed.verdictOf]
    exact (decide_eq_false_iff_not.2 fun h => hb true h).symm

/-- `buildTree` of the decoded moves is `buildTreeQ` of the raw outputs. -/
private theorem buildTree_eq_buildTreeQ {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → List Bool) :
    ∀ (b : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      buildTree (fun h => decodeOracleMove ℓ₁ (next h)) b hist = GGMRed.buildTreeQ next b hist
  | 0, hist => by
    rw [GGMRed.buildTreeQ_zero]
    unfold buildTree
    rw [decodeOracleMove_eq]
    cases GGMRed.queryOf ℓ₁ (next hist) <;> rfl
  | b + 1, hist => by
    rw [GGMRed.buildTreeQ_succ]
    unfold buildTree
    rw [decodeOracleMove_eq]
    cases GGMRed.queryOf ℓ₁ (next hist) with
    | none => rfl
    | some x =>
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
        (Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)))
  refine prgAdv_coins_equiv (G n) _ _ e fun z c => ?_
  obtain ⟨⟨W₁, W₂⟩, r⟩ := c
  refine GGMRed.ggmRedMachine_distinguisher hE D q i j (G n) (hG n) hi hj z (W₁, W₂) r
    (e ((W₁, W₂), r)) ?_
  show List.ofFn (Fin.appendEquiv (q.eval n * n) (q.eval n * (2 * n) + D.coinLen n)
    ((FunFamily.blocks (q.eval n) n).symm W₁,
      Fin.appendEquiv (q.eval n * (2 * n)) (D.coinLen n) (e₁ W₂, r))) = _
  rw [ofFn_appendEquiv, ofFn_appendEquiv]
  rfl

/-- **A next-query machine with query budget `0` has PRF advantage `0`:** with budget `0` the
tree `buildTree … 0 []` is a leaf whose verdict depends on the coins only, so both acceptance
probabilities are the same average over the coins (`uprob_snd`). -/
private theorem prfAdv_toOracleAdversary_zero
    (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) (D : NUPPT) (n : ℕ) :
    prfAdv (F n) (D.toOracleAdversary n n n 0) = 0 := by
  have hA : ∀ r, ∃ b : Bool, D.toOracleAdversary n n n 0 r = .ret b := by
    intro r
    unfold NUPPT.toOracleAdversary buildTree
    cases decodeOracleMove n (D.runAt n (encodeHist []) r) with
    | ret b => exact ⟨b, rfl⟩
    | query x => exact ⟨false, rfl⟩
  choose b hb using hA
  have key : ∀ {σ : Type} [Fintype σ] [Nonempty σ] (X : σ → (Fin n → Bool) → (Fin n → Bool)),
      acceptProb X (oracleDist (D.toOracleAdversary n n n 0)) =
        uprob fun r : D.Coins n => b r = true := by
    intro σ _ _ X
    unfold acceptProb
    rw [← uprob_snd (α := σ) (fun r : D.Coins n => b r = true)]
    refine uprob_congr fun z => ?_
    rw [oracleDist, hb z.2]
    rfl
  rw [prfAdv, distAdv, key, key, sub_self, abs_zero]

/-- **[PS10, Theorem 97.3] (Goldreich–Goldwasser–Micali): the GGM family of a length-doubling
pseudorandom generator is a pseudorandom function.**

**Proof sketch.** *Easy:* `exists_ggmPRF_evaluator` from `hG.easy`. *Pseudorandom:* fix a
next-query machine `D` and a budget `q`; we show `μ n := prfAdv (G n) (D^{(q n)})` is
negligible (`prfAdv_toOracleAdversary`). Suppose not; by `not_negligible_iff` there is `c` with
`μ n > 1/n^c` for infinitely many `n`. *Concrete step* (Thm-97.3.1, Thm-97.3.2): at every `n` with
`0 < n` and `0 < q n`, `exists_ggmBits_dist (G n) (D^{(q n)}) (toOracleAdversary_boundedBy …)`
gives indices `(i n, j n)` with `μ n / (n · q n) ≤ prgAdv (G n) (ggmBitsDist … (i n) (j n))`
(choose them by `Classical.choose`; put `(0, 0)` elsewhere). *Machine step* (Thm-97.3.3):
`exists_ggmBitsDist_nuppt hE hG D q i j` yields one non-uniform PPT `B` with
`prgAdv (G n) (B.distinguisher n (2n)) = prgAdv (G n) (ggmBitsDist … (i n) (j n))` at those `n`.
*Asymptotic step:* `hG.negligible_prgAdv B` says `ν n := prgAdv (G n) (B.distinguisher n (2n))`
is negligible, hence so is `n · q n · ν n` (`Negligible.mul_pow` with `q n ≤ C (n+1)^d` from
`PolyExpr.eval_le`, `Negligible.const_mul`, `Negligible.mono`), while `μ n ≤ n · q n · ν n`
infinitely often contradicts `μ n > 1/n^c` (`not_negligible_iff`); at the finitely many `n` with
`q n = 0` the adversary makes no query and `μ n = 0` (`buildTree` with budget `0` is a leaf
whose verdict does not depend on the oracle, `distAdv` of a constant distinguisher is `0`). -/
theorem ggmPRF_prf {G : ∀ n, (Fin n → Bool) → (Fin (2 * n) → Bool)} (hG : DoublingPRG G) :
    PRF (ggmPRF G) := by
  obtain ⟨E, hE, hGE⟩ := hG.easy
  refine ⟨exists_ggmPRF_evaluator hE hGE, fun D q => ?_⟩
  show Negligible fun n => prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n))
  by_contra hneg
  obtain ⟨c, hc⟩ := not_negligible_iff.1 hneg
  have hidx : ∀ n, 0 < n → 0 < q.eval n → ∃ (i : Fin n) (j : Fin (q.eval n)),
      prfAdv (ggmPRF G n) (D.toOracleAdversary n n n (q.eval n)) / (n * q.eval n) ≤
        prgAdv (G n) (ggmBitsDist (G n) (D.toOracleAdversary n n n (q.eval n)) (q.eval n) i j) :=
    fun n hn hq => exists_ggmBits_dist (G n) _ (D.toOracleAdversary_boundedBy n n n (q.eval n)) hn hq
  classical
  let i : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then (Classical.choose (hidx n h.1 h.2)).val else 0
  let j : ℕ → ℕ := fun n =>
    if h : 0 < n ∧ 0 < q.eval n then
      (Classical.choose (Classical.choose_spec (hidx n h.1 h.2))).val else 0
  obtain ⟨B, hB⟩ := exists_ggmBitsDist_nuppt hE hGE D q i j
  obtain ⟨n₀, hn₀⟩ := (hG.negligible_prgAdv B).polyExpr_mul (.mul .var q) c
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
