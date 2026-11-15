/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.Pseudorandom.Functions.Defs
import TCSlib.Cryptography.Pseudorandom.Functions.LazySampling

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Asymptotic oracle indistinguishability and pseudorandom functions

An oracle ensemble samples functions at each parameter. The next-query machine
sees the encoded history, uses one coin tape for the interaction, and runs within
an explicit query budget. The pseudorandom function contract combines an efficient
evaluator with indistinguishability from the random oracle [PS10, Definitions 96.1
and 96.2].

The concrete adversaries, random functions, and lazy runs come from [Gar26, §3.4].
The decoder treats malformed moves as rejection. A query after the budget is spent
also gives verdict `false` (foundation decision D7 of `PassShelatChapter2-4Plan.md`).

## Main definitions

* `TCSlib.Cryptography.OracleEnsemble` samples functions from finite seed types.
  `OracleEnsemble.random` uses the function table and `OracleEnsemble.keyed` uses a key.
* `TCSlib.Cryptography.OracleMove`, `decodeOracleMove`, and `encodeHist` specify the
  interface for a next-query machine. `buildTree` and `Complexity.NUPPT.toOracleAdversary`
  turn such a machine into a bounded query tree.
* `TCSlib.Cryptography.OracleEnsemble.Indist` gives the oracle indistinguishability
  condition. `TCSlib.Cryptography.PRF` packages that condition with efficient evaluation.

## Main results

* `TCSlib.Cryptography.acceptProb_random_eq_lazy` equates the two descriptions of a
  random function, by its table and by lazy sampling [PS10, §3.8.1].
* `Complexity.NUPPT.toOracleAdversary_boundedBy` gives the query bound.
* `TCSlib.Cryptography.OracleEnsemble.indist_iff` expresses the contract through
  negligible advantage. `TCSlib.Cryptography.oracle_hybrid_lemma` gives the
  finite hybrid bound for oracle ensembles.
* `TCSlib.Cryptography.prfAdv_toOracleAdversary` and `PRF.negligible_prfAdv`
  connect the PRF contract to the concrete advantage.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §3.8.1 and §3.8.2, Definitions 96.1 and 96.2.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (Definitions 3.6–3.9).
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
    (OracleEnsemble.random ℓ₁ ℓ₂).O n R = R :=
  randomFunction_apply _ _ R

/-- Unfolding: the keyed ensemble samples by `F n`. -/
@[simp] theorem OracleEnsemble.keyed_O {ℓ₁ ℓ₂ : PolyExpr}
    (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) (n : ℕ)
    (s : Fin n → Bool) : (OracleEnsemble.keyed F).O n s = F n s := rfl

/-- Acceptance against the random oracle ensemble is acceptance against a uniform function
table, with the same oracle adversary and its coins. -/
theorem OracleEnsemble.acceptProb_random_eq {ρ : Type*} [Fintype ρ] (ℓ₁ ℓ₂ : PolyExpr) (n : ℕ)
    (A : OracleAdversary ρ (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) :
    acceptProb ((OracleEnsemble.random ℓ₁ ℓ₂).O n) (oracleDist A) =
      acceptProb (randomFunction (Fin (ℓ₁.eval n) → Bool) (Fin (ℓ₂.eval n) → Bool)) (oracleDist A) :=
  rfl

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
  rw [acceptProb_def, acceptProb_def,
    uprob_prod_comm (fun R (r : ρ) => oracleDist A ((OracleEnsemble.random ℓ₁ ℓ₂).O n R) r = true),
    uprob_prod_comm (fun W (r : ρ) => lazyDist A (extendStream W) r = true),
    uprob_prod, uprob_prod]
  congr 1
  funext r
  simp only [OracleEnsemble.random_O, oracleDist_apply, lazyDist_apply]
  exact (QueryTree.uprob_evalLazy (· = true) ((OracleAdversary.boundedBy_iff A q).1 hA r)).symm

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

/-- The two-bit word `[true, b]` is not a pair: its decoding would start with a doubled bit
(at least four bits) or with the separator `01`. -/
theorem pairDecode_true_two (b : Bool) : pairDecode [true, b] = none := by
  cases h : pairDecode [true, b] with
  | none => rfl
  | some p =>
    obtain ⟨u, v⟩ := p
    have hz := eq_pairEncode_of_pairDecode _ u v h
    rw [pairEncode_eq] at hz
    cases u with
    | nil => simp at hz
    | cons x u =>
      have hl := congrArg List.length hz
      simp only [List.length_cons, List.length_append, List.flatMap_cons, List.length_nil] at hl
      omega

/-- Decoding a pair `⟨[false], x⟩`: the query `x` when `x` has `ℓ₁` bits, else the verdict
`false`: `decodeOracleMove ℓ₁ (pairEncode [false] x) =
match decodeFin ℓ₁ x with | some y => .query y | none => .ret false`. -/
theorem decodeOracleMove_pairEncode_false (ℓ₁ : ℕ) (x : List Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] x) =
      match decodeFin ℓ₁ x with
      | some y => .query y
      | none => .ret false := by
  unfold decodeOracleMove
  rw [pairDecode_pairEncode, pairEncode_eq]
  rfl

/-- Decoding the two-bit word `[true, b]`: the verdict `b`,
`decodeOracleMove ℓ₁ [true, b] = .ret b`. -/
theorem decodeOracleMove_true_two (ℓ₁ : ℕ) (b : Bool) :
    decodeOracleMove ℓ₁ [true, b] = .ret b := by
  unfold decodeOracleMove
  rw [pairDecode_true_two]

/-- Decoding a well-formed query word: for every `ℓ₁`-bit string `x` (`ℓ₁ = 0` included),
`decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x`. -/
theorem decodeOracleMove_pairEncode_ofFn (ℓ₁ : ℕ) (x : Fin ℓ₁ → Bool) :
    decodeOracleMove ℓ₁ (pairEncode [false] (List.ofFn x)) = .query x := by
  rw [decodeOracleMove_pairEncode_false, decodeFin_ofFn]

/-- Decoding a query-shaped word of the wrong length: if `|x| ≠ ℓ₁` then
`decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false`. -/
theorem decodeOracleMove_pairEncode_false_of_length_ne (ℓ₁ : ℕ) {x : List Bool}
    (hx : x.length ≠ ℓ₁) : decodeOracleMove ℓ₁ (pairEncode [false] x) = .ret false := by
  rw [decodeOracleMove_pairEncode_false]
  cases h : decodeFin ℓ₁ x with
  | none => rfl
  | some y => exact absurd (length_eq_of_decodeFin_eq_some h) hx

/-- **The malformed branch**: a word that is neither a query-shaped pair `⟨[false], x⟩` (for any
string `x`) nor a two-bit verdict word `[true, b]` decodes to the verdict `false`:
`decodeOracleMove ℓ₁ w = .ret false`. Together with `decodeOracleMove_pairEncode_ofFn`,
`decodeOracleMove_pairEncode_false_of_length_ne` and `decodeOracleMove_true_two` this covers every
word, for every `ℓ₁`.

**Proof sketch.** Along the match of `decodeOracleMove`: a decoding
`pairDecode w = some ([false], x)` gives `w = ⟨[false], x⟩` (`eq_pairEncode_of_pairDecode`),
excluded; the word `[true, b]` is excluded; the remaining branch is `.ret false`. -/
theorem decodeOracleMove_of_ne (ℓ₁ : ℕ) {w : List Bool} (hq : ∀ x, w ≠ pairEncode [false] x)
    (hv : ∀ b, w ≠ [true, b]) : decodeOracleMove ℓ₁ w = .ret false := by
  unfold decodeOracleMove
  split
  · rename_i w' o w'' x hx
    exact absurd (eq_pairEncode_of_pairDecode w' _ _ hx) (hq x)
  · rename_i o w' b hp
    exact absurd rfl (hv b)
  · rfl

/-- The encoding of the history of (query, answer) pairs handed to a next-query machine: the
nested pair `⟨⟨x₁, y₁⟩, ⟨⟨x₂, y₂⟩, ⟨…, []⟩⟩⟩`. -/
def encodeHist {ℓ₁ ℓ₂ : ℕ} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool :=
  h.foldr (fun p acc => pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) acc) []

/-- The empty history is encoded as the empty string: `encodeHist [] = []`. -/
theorem encodeHist_nil {ℓ₁ ℓ₂ : ℕ} :
    encodeHist ([] : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) = [] :=
  rfl

/-- A history is encoded pair by pair:
`encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h)`. -/
theorem encodeHist_cons {ℓ₁ ℓ₂ : ℕ} (p : (Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))
    (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) :
    encodeHist (p :: h) = pairEncode (pairEncode (List.ofFn p.1) (List.ofFn p.2)) (encodeHist h) :=
  rfl

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

section BuildTree

variable {ℓ₁ ℓ₂ : ℕ} {next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁}
  {hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))}

/-- With the budget spent, a verdict stops the tree: `buildTree next 0 hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_zero_of_ret {b : Bool} (h : next hist = .ret b) :
    buildTree next 0 hist = .ret b := by
  rw [buildTree, h]

/-- With the budget spent, a query gives the forced verdict `false`:
`buildTree next 0 hist = ret false` when `next hist = query x`. -/
theorem buildTree_zero_of_query {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next 0 hist = .ret false := by
  rw [buildTree, h]

/-- Within budget, a verdict stops the tree: `buildTree next (q + 1) hist = ret b` when
`next hist = ret b`. -/
theorem buildTree_succ_of_ret {q : ℕ} {b : Bool} (h : next hist = .ret b) :
    buildTree next (q + 1) hist = .ret b := by
  rw [buildTree, h]

/-- Within budget, a query becomes a query node whose continuation appends the answer:
`buildTree next (q + 1) hist = query x (fun o => buildTree next q (hist ++ [(x, o)]))` when
`next hist = query x`. -/
theorem buildTree_succ_of_query {q : ℕ} {x : Fin ℓ₁ → Bool} (h : next hist = .query x) :
    buildTree next (q + 1) hist = .query x (fun o => buildTree next q (hist ++ [(x, o)])) := by
  rw [buildTree, h]

end BuildTree

/-- The tree built with budget `q` makes at most `q` queries, from every starting history. -/
theorem buildTree_boundedBy {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))),
      (buildTree next q hist).BoundedBy q
  | 0, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_zero_of_ret h]; exact QueryTree.boundedBy_ret b 0
    | query x => rw [buildTree_zero_of_query h]; exact QueryTree.boundedBy_ret false 0
  | q + 1, hist => by
    cases h : next hist with
    | ret b => rw [buildTree_succ_of_ret h]; exact QueryTree.boundedBy_ret b (q + 1)
    | query x =>
      rw [buildTree_succ_of_query h]
      exact (QueryTree.boundedBy_query_succ x _ q).2
        fun o => buildTree_boundedBy next q (hist ++ [(x, o)])

/-- The query tree of the next-query machine `D` at parameter `n` with budget `q`
([PS10, Definition 96.1]; D7: no oracle tapes, one activation per query on the history). The
machine `D(1^n, ·)` is run, with one random tape `r` for the whole interaction, on the
encoded history; its output is decoded as a query or a verdict. -/
def _root_.Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) :=
  fun r => buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []

/-- The tree of `D` on the coins `r` is built from the empty history, the next move being `D`'s
output on the encoded history, decoded:
`D.toOracleAdversary n ℓ₁ ℓ₂ q r =
buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []`. -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_eq (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ)
    (r : D.Coins n) :
    D.toOracleAdversary n ℓ₁ ℓ₂ q r =
      buildTree (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q [] :=
  rfl

/-- The oracle adversary of a next-query machine with budget `q` makes at most `q` queries on
every coin string (the hypothesis `BoundedBy` of `ggm_prfAdv_le` and `exists_ggmBits_dist`).
Induction on the budget (`buildTree_boundedBy`). -/
theorem _root_.Complexity.NUPPT.toOracleAdversary_boundedBy (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) :
    (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q :=
  (OracleAdversary.boundedBy_iff _ q).2 fun r => by
    rw [NUPPT.toOracleAdversary_eq]
    exact buildTree_boundedBy _ q []

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

/-- Oracle ensembles are indistinguishable iff the oracle advantage is negligible for
each next-query machine and polynomial query budget. -/
theorem OracleEnsemble.indist_iff {ℓ₁ ℓ₂ : PolyExpr} (O O' : OracleEnsemble ℓ₁ ℓ₂) :
    O.Indist O' ↔ ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n =>
      distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n))) :=
  Iff.rfl

/-- **Reflexivity of oracle indistinguishability** (non-vacuity of
[PS10, Definition 96.1]): every oracle ensemble is indistinguishable from itself, the
advantage being identically `0`. -/
theorem OracleEnsemble.Indist.refl {ℓ₁ ℓ₂ : PolyExpr} (O : OracleEnsemble ℓ₁ ℓ₂) : O.Indist O := by
  intro D q
  have h : (fun n => distAdv (O.O n) (O.O n)
      (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))) = fun _ => 0 := by
    funext n
    simp [distAdv_def]
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
    rw [distAdv_def, distAdv_def]
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
  simp only [distAdv_def, abs_abs]
  exact (abs_sub_le _ _ _).trans (le_abs_self _)

/-- **The hybrid lemma for oracles** [PS10, §3.8.2, "oracle indistinguishability satisfies …
the Hybrid Lemma"] (Claim-96.b), at one parameter: if the oracle adversary `A` distinguishes
the oracle distributions `H 0` and `H m` with advantage `ε`, then it distinguishes some
consecutive pair `H i, H (i+1)` (`i < m`) with advantage at least `ε / m`. Apply the
finite hybrid bound `exists_hybrid_gap` to the acceptance probabilities for `oracleDist A`. -/
theorem oracle_hybrid_lemma {σ : Type*} {I O : Type} {ρ : Type*} [Fintype σ] [Fintype ρ] {m : ℕ} (hm : 0 < m)
    (H : ℕ → σ → (I → O)) (A : OracleAdversary ρ I O) :
    ∃ i < m, distAdv (H 0) (H m) (oracleDist A) / m ≤ distAdv (H i) (H (i + 1)) (oracleDist A) := by
  simpa only [distAdv_def] using exists_hybrid_gap (fun i => acceptProb (H i) (oracleDist A)) hm

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
      prfAdv (F n) (D.toOracleAdversary n n n q) := by
  rw [prfAdv_def]
  rfl

/-- **Pseudorandomness unfolded**: for a PRF `F`, every next-query machine `D` with every
polynomial budget `q` has negligible concrete PRF advantage `prfAdv (F n) (D^{(q n)})` — the
form in which the Garg-layer reductions consume [PS10, Definition 96.2]. -/
theorem PRF.negligible_prfAdv {F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)}
    (hF : PRF F) (D : NUPPT) (q : PolyExpr) :
    Negligible fun n => prfAdv (F n) (D.toOracleAdversary n n n (q.eval n)) := by
  exact (congrArg Negligible (funext fun n => prfAdv_toOracleAdversary F D n (q.eval n))).mp
    (hF.pseudorandom D q)

end TCSlib.Cryptography
