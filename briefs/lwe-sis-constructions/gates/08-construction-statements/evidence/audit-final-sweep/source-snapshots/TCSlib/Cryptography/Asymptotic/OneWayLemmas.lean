/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Complexity.Randomized.Repetition
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.OneWayFunctions.Amplification
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the one-way function theorems

The machine-level and list-level infrastructure behind the fills of
`TCSlib.Cryptography.Asymptotic.OneWay` ([PS10, Theorems 35.1 and 35.2]): the file is
imported by `OneWay.lean`, so it cannot mention `FunFamily`; every statement is about strings,
`Fin`-indexed tuples (blocks through `finProdFinEquiv`), the concrete experiments of
`TCSlib.Cryptography.Foundations.Experiments` and the machine calculus of
`TCSlib.Complexity.Randomized`.

* **Blocks of a string.** A string of `q·ℓ` bits is `q` consecutive blocks of `ℓ` bits; block `i`
  of `x : Fin (q·ℓ) → Bool` is `fun j => x (finProdFinEquiv (i, j))` (the `blocks` bijection of
  `OneWay.lean` unfolds to this), and `ofFn_block_eq_take_drop` reads it off `List.ofFn x` by
  `drop`/`take`.
* **Planting** (`invProbOpt_prodFun_le_yaoTryOpt`): the `Option`-valued form of
  `OneWay.invProb_prodFun_le_yaoTry` — planting a challenge at a fixed position of a fresh tuple
  inverts `f` at least as often as the given inverter inverts the direct product.
* **Bridges** between the `List.find?` of `Complexity.polyTimeComputable_iterateFind` and the
  `foldr`/`findSome?` of `OneWay.yaoInverter` and `rejectionSample`.
* **Statistical closeness of products** over `Fin N` (`statClose_pi`): the `T + 1` rounds of
  rejection-sampled positions of Algorithm 38.5 are within `(T + 1)·δ` of uniform.
* **Sub-machines** of Algorithm 38.5 as `PolyTimeComputable` functions with clean
  specifications: the blockwise evaluator `exists_prodEval` (the honest evaluator of the direct
  product and of the fresh tuple `(f(x₁), …, f(x_m))`), the capped binary-to-unary converter
  `exists_unaryOf`, and the rejection sampler of the position `exists_posMachine`.

## Main definitions

* `TCSlib.Cryptography.OneWay.bitListToNat` — a bit string read as a number, most significant bit
  first (the list form of `bitsToNat`).
* `TCSlib.Cryptography.OneWay.padTrue` — pad or truncate a string to `ℓ` bits with `true`.

## Main results

* `TCSlib.Cryptography.OneWay.invProbOpt_prodFun_le_yaoTryOpt` — one-call planting, `Option` form.
* `TCSlib.Cryptography.OneWay.statClose_pi` — closeness of `Fin N`-indexed products.
* `TCSlib.Cryptography.OneWay.exists_prodEval`, `exists_unaryOf`, `exists_posMachine` — the
  sub-machines of [PS10, Algorithm 38.5].
* `TCSlib.Cryptography.OneWay.foldr_ite_eq_find?`, `findSome?_eq_bind_find?`,
  `find?_range_eq_map_find?_finRange` — loop bridges.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4: Theorems 35.1, 35.2 and Algorithm 38.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Theorem 2.1, Figure 2.2: the concrete amplification).
-/

namespace TCSlib.Cryptography.OneWay

open Complexity Turing Finset

/-! ### Blocks of a string -/

/-- Block `i` of `x : Fin (q * ℓ) → Bool` (positions `ℓ·i, …, ℓ·i + ℓ - 1`) is the `ℓ`-bit window
of `List.ofFn x` after `i·ℓ` bits. -/
theorem ofFn_block_eq_take_drop {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    List.ofFn (fun j : Fin ℓ => x (finProdFinEquiv (i, j))) =
      ((List.ofFn x).drop (i * ℓ)).take ℓ := by
  have hle : i * ℓ + ℓ ≤ q * ℓ := by
    have : (i + 1) * ℓ ≤ q * ℓ := Nat.mul_le_mul_right ℓ i.2
    rwa [Nat.add_mul, Nat.one_mul] at this
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop]
  congr 1
  ext
  simp only [finProdFinEquiv_apply_val]
  ring

/-- The window of `ℓ` bits after `i·ℓ` bits of `List.ofFn x` has exactly `ℓ` bits. -/
theorem length_take_drop_block {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    (((List.ofFn x).drop (i * ℓ)).take ℓ).length = ℓ := by
  rw [← ofFn_block_eq_take_drop, List.length_ofFn]

/-- The concatenation of two chunks indexed by `Fin 2`. -/
theorem flatten_ofFn_two (g : Fin 2 → List Bool) : (List.ofFn g).flatten = g 0 ++ g 1 := by
  simp [List.ofFn_succ]

/-- Reading the first `m` coordinates of a tuple is taking the first `m` bits of its encoding. -/
theorem ofFn_castLE_eq_take {m k : ℕ} (h : m ≤ k) (a : Fin k → Bool) :
    List.ofFn (fun j : Fin m => a (Fin.castLE h j)) = (List.ofFn a).take m := by
  refine List.ext_getElem (by simp; omega) fun j h₁ h₂ => ?_
  simp

/-- Pad with `true` or truncate a string to exactly `ℓ` bits (the convention of the block
extraction of Algorithm 38.5: a malformed answer of the given inverter is padded). -/
def padTrue (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool := fun i => w.getD i true

/-- The encoding of `padTrue ℓ w` is `w` padded with `1^ℓ` and cut to `ℓ` bits. -/
theorem ofFn_padTrue (ℓ : ℕ) (w : List Bool) :
    List.ofFn (padTrue ℓ w) = (w ++ List.replicate ℓ true).take ℓ := by
  refine List.ext_getElem (by simp) fun j h₁ h₂ => ?_
  simp only [List.getElem_ofFn, padTrue, List.getElem_take]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj : j < w.length
  · rw [List.getElem_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
  · rw [List.getElem_append_right (not_lt.1 hj), List.getElem_replicate,
      List.getElem?_eq_none (not_lt.1 hj), Option.getD_none]

/-- Padding the encoding of an `ℓ`-bit string returns it. -/
theorem padTrue_ofFn {ℓ : ℕ} (x : Fin ℓ → Bool) : padTrue ℓ (List.ofFn x) = x := by
  funext i
  simp [padTrue]

/-- Padding the tail of the encoding of a `q·ℓ`-bit tuple after `i·ℓ` bits gives block `i`. -/
theorem padTrue_drop_ofFn {q ℓ : ℕ} (x : Fin (q * ℓ) → Bool) (i : Fin q) :
    padTrue ℓ ((List.ofFn x).drop (i * ℓ)) = fun j => x (finProdFinEquiv (i, j)) := by
  apply List.ofFn_injective
  rw [ofFn_padTrue, ofFn_block_eq_take_drop]
  have h := length_take_drop_block x i
  rw [List.length_take] at h
  rw [List.take_append_of_le_length (by omega)]

/-- A bit string read as a number, most significant bit first: the list form of `bitsToNat`
(`bitsToNat b = bitListToNat (List.ofFn b)` by definition). -/
def bitListToNat (l : List Bool) : ℕ := l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- `bitsToNat` is `bitListToNat` of the encoding. -/
theorem bitsToNat_eq_bitListToNat {k : ℕ} (b : Fin k → Bool) : bitsToNat b = bitListToNat (List.ofFn b) :=
  rfl

/-- Reading one more bit: `bitListToNat (l ++ [c]) = 2 · bitListToNat l + c`. -/
theorem bitListToNat_append_singleton (l : List Bool) (c : Bool) :
    bitListToNat (l ++ [c]) = 2 * bitListToNat l + (if c then 1 else 0) := by
  simp [bitListToNat, List.foldl_append]

/-- Prefix values are monotone: the number read from a prefix is at most the number read from
the whole string.

**Proof sketch.** Induction on the string: reading the remaining bits after a prefix of value
`a` gives `a · 2^{rest} + value(rest)`, so a longer suffix can only increase the value
(`Nat.pow_le_pow_right`). -/
theorem bitListToNat_take_le (l : List Bool) : ∀ i, bitListToNat (l.take i) ≤ bitListToNat l := by
  intro i
  induction l generalizing i with
  | nil => simp [bitListToNat]
  | cons c l ih =>
    cases i with
    | zero => simp [bitListToNat]
    | succ i =>
      rw [List.take_succ_cons]
      have key : ∀ (m : List Bool) (a : ℕ),
          m.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
            a * 2 ^ m.length + m.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
        intro m
        induction m with
        | nil => simp
        | cons d m ihm =>
          intro a
          rw [List.foldl_cons, List.foldl_cons, ihm, ihm (2 * 0 + _), List.length_cons, pow_succ]
          ring
      simp only [bitListToNat, List.foldl_cons] at ih ⊢
      rw [key (l.take i), key l]
      have h1 := ih i
      have h2 : (l.take i).length ≤ l.length := List.length_take_le' _ _
      have h3 : 2 ^ (l.take i).length ≤ 2 ^ l.length := Nat.pow_le_pow_right (by norm_num) h2
      have h4 : 0 ≤ (if c then 1 else 0 : ℕ) := Nat.zero_le _
      nlinarith [Nat.mul_le_mul_left (2 * 0 + (if c then 1 else 0)) h3]

/-! ### Planting, `Option` form -/

/-- **One-call planting, `Option` form** (the `invProbOpt` variant of
`OneWay.invProb_prodFun_le_yaoTry`, anticipated by the proof sketch of [PS10, Theorem 35.2]):
for a possibly failing inverter `B` of the direct product and a fixed position `i`, the
inverter that samples a fresh tuple, plants the challenge at position `i`, calls `B` and returns
the `i`-th component of its answer inverts `f` at least as often as `B` inverts `prodFun f q`.

**Proof sketch.** As `invProb_prodFun_le_yaoTry`: the planted tuple is uniform
(`OneWay.uprob_update`, `prodFun_update`), and an inverse of the whole tuple inverts every
coordinate (`uprob_mono`). -/
theorem invProbOpt_prodFun_le_yaoTryOpt {α β ρ : Type*} [Fintype α] [Nonempty α] [DecidableEq β]
    [Fintype ρ] {q : ℕ} (f : α → β) (B : (Fin q → β) → ρ → Option (Fin q → α)) (i : Fin q) :
    invProbOpt (prodFun f q) B ≤
      invProbOpt f fun y (c : (Fin q → α) × ρ) =>
        (B (Function.update (prodFun f q c.1) i y) c.2).map fun xs => xs i := by
  unfold invProbOpt
  have h := uprob_update (α := α) (ρ := ρ) i fun xs r =>
    ∃ x', (B (prodFun f q xs) r).map (fun xs => xs i) = some x' ∧ f x' = f (xs i)
  simp only [prodFun_update, Function.update_self] at h
  refine le_trans ?_ (le_of_eq h.symm)
  apply uprob_mono
  rintro ⟨xs, r⟩ ⟨xs', hxs', hf⟩
  exact ⟨xs' i, by simp [hxs'], congrFun hf i⟩

/-! ### Loop bridges -/

/-- The `foldr` of `OneWay.yaoInverter` returns the value at the first element satisfying the
test, or the default (`Option.elim` of the `List.find?`). -/
theorem foldr_ite_eq_find? {ι γ : Type*} (P : ι → Prop) [DecidablePred P] (v : ι → γ) (d : γ) :
    ∀ l : List ι, l.foldr (fun t acc => if P t then v t else acc) d =
      (l.find? (fun t => decide (P t))).elim d v := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.foldr_cons, List.find?_cons, ih]
    by_cases h : P t <;> simp [h]

/-- `findSome?` is `find?` of the successful indices followed by the function. -/
theorem findSome?_eq_bind_find? {ι γ : Type*} (f : ι → Option γ) :
    ∀ l : List ι, l.findSome? f = (l.find? fun t => (f t).isSome).bind f := by
  intro l
  induction l with
  | nil => rfl
  | cons t l ih =>
    rw [List.findSome?_cons, List.find?_cons]
    cases hf : f t <;> simp [hf, ih]

/-- A search over `List.range N` with a test that agrees with `p` below `n ≤ N` and fails from
`n` on is the search over `List.finRange n`. -/
theorem find?_range_eq_map_find?_finRange {n N : ℕ} (hN : n ≤ N) (p : Fin n → Bool) (p' : ℕ → Bool)
    (hp : ∀ (t : ℕ) (h : t < n), p' t = p ⟨t, h⟩) (hp' : ∀ t, n ≤ t → p' t = false) :
    (List.range N).find? p' = ((List.finRange n).find? p).map Fin.val := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hN
  induction d with
  | zero =>
    rw [Nat.add_zero, ← List.map_coe_finRange, List.find?_map]
    congr 2
    funext t
    exact hp t.1 t.2
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.find?_append, ih (Nat.le_add_right n d)]
    have : [n + d].find? p' = none := by simp [hp' (n + d) (Nat.le_add_right n d)]
    rw [this, Option.or_none]

/-! ### The direct product's evaluator -/

/-- The concatenation of `R` chunks of which only the first `Q ≤ R` are nonempty is the
concatenation of the first `Q`. -/
theorem flatMap_range_ite_eq_flatten_ofFn (E : ℕ → List Bool) {Q R : ℕ} (h : Q ≤ R) :
    (List.range R).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
  have base : (List.range Q).flatMap (fun i => if Q ≤ i then [] else E i) =
      (List.ofFn fun j : Fin Q => E j).flatten := by
    rw [List.ofFn_eq_map, List.flatMap_def, ← List.map_coe_finRange, List.map_map]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp]
    rw [if_neg (not_le.2 t.2)]
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => simpa using base
  | succ d ih =>
    rw [← Nat.add_assoc, List.range_succ, List.flatMap_append]
    have : [Q + d].flatMap (fun i => if Q ≤ i then [] else E i) = [] := by
      simp [Nat.le_add_right Q d]
    rw [this, List.append_nil]
    exact ih (Nat.le_add_right Q d)

/-! ### Statistical closeness of `Fin N`-indexed products -/

/-- **Closeness of products over `Fin N`:** if `X` is `δ`-close to `Y` then `N` independent
copies are `N·δ`-close (the `T + 1` rounds of rejection-sampled positions of
[PS10, Algorithm 38.5] are within `(T + 1)·δ` of uniform).

**Proof sketch.** Induction on `N`. For `N = 0` both samplers are constant. For `N + 1`,
split off the first coordinate with `Fin.consEquiv`: the pair sampler is `StatClose.prod` of
one copy and `N` copies (`δ + N·δ`), post-processed by `Fin.cons` (`StatClose.map`) and
re-indexed by the bijection on both sides (`StatClose.comp_equiv_left/right`);
`Fin.cons (c 0) (Fin.tail c) = c` identifies the samplers. -/
theorem statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (N : ℕ) :
    StatClose (fun c : Fin N → σ => fun t => X (c t)) (fun c : Fin N → τ => fun t => Y (c t))
      (N * δ) := by
  induction N with
  | zero =>
    intro T
    have hX : ∀ c : Fin 0 → σ, (fun t => X (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    have hY : ∀ c : Fin 0 → τ, (fun t => Y (c t)) = (fun t : Fin 0 => t.elim0) :=
      fun c => funext fun t => t.elim0
    simp only [hX, hY, Nat.cast_zero, zero_mul]
    by_cases hT : T (fun t : Fin 0 => t.elim0)
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | succ N ih =>
    have hp := ((h.prod ih).map (fun p : γ × (Fin N → γ) => (Fin.cons p.1 p.2 : Fin (N + 1) → γ)))
    have hp2 := (hp.comp_equiv_left (Fin.consEquiv (fun _ => σ)).symm).comp_equiv_right
      (Fin.consEquiv (fun _ => τ)).symm
    have keyX : ∀ c : Fin (N + 1) → σ,
        (Fin.cons (X (c 0)) (fun t => X (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => X (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail]
    have keyY : ∀ c : Fin (N + 1) → τ,
        (Fin.cons (Y (c 0)) (fun t => Y (Fin.tail c t)) : Fin (N + 1) → γ) = fun t => Y (c t) := by
      intro c
      funext t
      refine Fin.cases ?_ (fun t => ?_) t
      · simp
      · simp [Fin.tail]
    have hδ : ((N + 1 : ℕ) : ℝ) * δ = δ + N * δ := by push_cast; ring
    rw [hδ]
    convert hp2 using 1
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyX c).symm
    · funext c
      simp only [Fin.consEquiv_symm_apply]
      exact (keyY c).symm

/-! ### Unary multiplication at the FP level -/

/-- The FP form of the unary-multiplication machine: `⟨u, v⟩ ↦ 1^{|u|·|v|}` (with the total
projections, so `[]` on malformed words). -/
theorem polyTimeComputable_unaryMulPair :
    PolyTimeComputable fun z => List.replicate ((pairFstD z).length * (pairSndD z).length) true := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  have h : PolyTimeComputable (fun z => match pairDecode z with
      | some (u, v) => List.replicate (u.length * v.length) true
      | none => []) := ⟨M, c, 2, hM⟩
  convert h using 1
  funext z
  cases hz : pairDecode z with
  | none => simp [pairFstD, pairSndD, hz]
  | some p =>
    obtain ⟨u, v⟩ := p
    have := eq_pairEncode_of_pairDecode z u v hz
    subst this
    simp

/-! ### The blockwise evaluator -/

namespace ProdEval

/-- The parameter slot `u` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def u (w : List Bool) : List Bool := pairFstD (pairFstD w)

/-- The unary round counter `cnt` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def cnt (w : List Bool) : List Bool := pairSndD (pairFstD w)

/-- The unread input `rest` of the state word `⟨⟨u, cnt⟩, rest⟩`. -/
def rest (w : List Bool) : List Bool := pairSndD w

/-- The initial state word `⟨⟨u, []⟩, x⟩` of the input `⟨u, x⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairEncode (pairFstD z) []) (pairSndD z)

/-- One round: add a token to the counter and drop one block of `inLen(|u|)` bits. -/
def step (inLen : PolyExpr) (w : List Bool) : List Bool :=
  pairEncode (pairEncode (u w) (true :: cnt w)) ((rest w).drop (inLen.eval (u w).length))

/-- The emission of a round: `F ⟨u, next block⟩` while fewer than `q(|u|)` rounds have run,
`[]` afterwards. -/
def emit (F : List Bool → List Bool) (inLen q : PolyExpr) (w : List Bool) : List Bool :=
  if q.eval (u w).length ≤ (cnt w).length then []
  else F (pairEncode (u w) ((rest w).take (inLen.eval (u w).length)))

/-- The parameter slot is polynomial-time. -/
theorem u_poly : PolyTimeComputable u := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The counter is polynomial-time. -/
theorem cnt_poly : PolyTimeComputable cnt :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread input is polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  (polyTimeComputable_pairFstD.pairEncode (polyTimeComputable_const [])).pairEncode
    polyTimeComputable_pairSndD

/-- Dropping the current block is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly`
on `⟨u, rest⟩`). -/
theorem drop_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).drop (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairDropPoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- Reading the current block is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly`
on `⟨u, rest⟩`). -/
theorem take_poly (inLen : PolyExpr) :
    PolyTimeComputable fun w => (rest w).take (inLen.eval (u w).length) := by
  convert (polyTimeComputable_pairTakePoly inLen).comp (u_poly.pairEncode rest_poly) using 1
  funext w
  simp

/-- The step is polynomial-time. -/
theorem step_poly (inLen : PolyExpr) : PolyTimeComputable (step inLen) :=
  (u_poly.pairEncode ((StateLoop.cons_poly true).comp cnt_poly)).pairEncode (drop_poly inLen)

/-- The emission is polynomial-time (`StateLoop.lenLe_comp` against `1^{q(|u|)}`,
`Complexity.polyTimeComputable_ite`). -/
theorem emit_poly {F : List Bool → List Bool} (hF : PolyTimeComputable F) (inLen q : PolyExpr) :
    PolyTimeComputable (emit F inLen q) := by
  have htest : PolyTimeComputable fun w => [decide (q.eval (u w).length ≤ (cnt w).length)] := by
    convert StateLoop.lenLe_comp cnt_poly (StateLoop.unaryPoly_comp q u_poly) using 1
    funext w
    simp
  convert polyTimeComputable_ite htest (polyTimeComputable_const [])
    (hF.comp (u_poly.pairEncode (take_poly inLen))) using 1
  funext w
  by_cases h : q.eval (u w).length ≤ (cnt w).length <;> simp [emit, h]

/-- The orbit of an arbitrary word after `i + 1` rounds: the parameter is retained, the counter
has grown by `i + 1` tokens and `(i + 1)` blocks have been dropped. -/
theorem iterate_step_succ (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    (step inLen)^[i + 1] w =
      pairEncode (pairEncode (u w) (List.replicate (i + 1) true ++ cnt w))
        ((rest w).drop ((i + 1) * inLen.eval (u w).length)) := by
  induction i with
  | zero => simp [step]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, u, cnt, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
    congr 2
    ring

/-- The orbit of an arbitrary word `w` stays within `4|w| + 2i + 6` after `i` rounds. -/
theorem length_iterate_step_le (inLen : PolyExpr) (w : List Bool) (i : ℕ) :
    ((step inLen)^[i] w).length ≤ 4 * w.length + 2 * i + 6 := by
  cases i with
  | zero => simp; omega
  | succ i =>
    rw [iterate_step_succ, length_pairEncode, length_pairEncode, List.length_append,
      List.length_replicate]
    have h1 := StateLoop.length_pairFstD_add_pairSndD_le w
    have h2 := StateLoop.length_pairFstD_add_pairSndD_le (pairFstD w)
    have h3 : ((rest w).drop ((i + 1) * inLen.eval (u w).length)).length =
        (rest w).length - (i + 1) * inLen.eval (u w).length := List.length_drop
    simp only [u, cnt, rest] at h2 h3 ⊢
    omega

/-- The orbit on a genuine input `⟨⟨1^n, []⟩, x⟩`: `⟨⟨1^n, 1^i⟩, x.drop (i·inLen(n))⟩`. -/
theorem iterate_step_start (inLen : PolyExpr) (n : ℕ) (x : List Bool) (i : ℕ) :
    (step inLen)^[i] (start (pairEncode (List.replicate n true) x)) =
      pairEncode (pairEncode (List.replicate n true) (List.replicate i true))
        (x.drop (i * inLen.eval n)) := by
  cases i with
  | zero => simp [start]
  | succ i =>
    rw [iterate_step_succ]
    simp [start, u, cnt, rest]

end ProdEval

/-- **The blockwise evaluator** (the honest evaluator of the direct product of
[PS10, Theorem 35.1], and the evaluation of the fresh tuple of Algorithm 38.5): from a
polynomial-time `F` and syntactic lengths `inLen`, `q`, a polynomial-time `F'` with
`F' ⟨1^n, x⟩ = F ⟨1^n, x₀⟩ ++ ⋯ ++ F ⟨1^n, x_{q(n)-1}⟩` on every `q(n)·inLen(n)`-bit `x`
(`x_i` its `i`-th block).

**Proof sketch.** `Complexity.polyTimeComputable_iterateEmit` with `R := q` on the state word
`⟨⟨1^n, cnt⟩, rest⟩` (`ProdEval`): each round emits `F ⟨1^n, rest.take (inLen n)⟩` while the
unary counter is shorter than `1^{q(n)}` and `[]` afterwards, then drops `inLen n` bits and adds
a token (`ProdEval.iterate_step_start`); the orbit of every word is bounded by
`4|w| + 2q(|w|) + 6` (`ProdEval.length_iterate_step_le`). `q` is evaluated at the length of the
state word `≥ n`, so at least `q(n)` rounds emit (`PolyExpr.eval_mono`); the concatenation
of the first `q(n)` emissions is the target by `flatMap_range_ite_eq_flatten_ofFn` and
`ofFn_block_eq_take_drop`. -/
theorem exists_prodEval {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (inLen q : PolyExpr) :
    ∃ F' : List Bool → List Bool, PolyTimeComputable F' ∧
      ∀ (n : ℕ) (x : Fin (q.eval n * inLen.eval n) → Bool),
        F' (pairEncode (List.replicate n true) (List.ofFn x)) =
          (List.ofFn fun i : Fin (q.eval n) =>
            F (pairEncode (List.replicate n true)
              (List.ofFn fun j : Fin (inLen.eval n) => x (finProdFinEquiv (i, j))))).flatten := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ q.eval w.length →
      ((ProdEval.step inLen)^[i] w).length ≤
        (PolyExpr.add (.mul (.const 4) .var) (.add (.mul (.const 2) q) (.const 6))).eval w.length := by
    intro w i hi
    have := ProdEval.length_iterate_step_le inLen w i
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hloop := polyTimeComputable_iterateEmit (ProdEval.step_poly inLen)
    (ProdEval.emit_poly hF inLen q) q _ horbit
  refine ⟨_, hloop.comp ProdEval.start_poly, fun n x => ?_⟩
  simp only [Function.comp_apply]
  have hlen : n ≤ (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length := by
    simp only [ProdEval.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_replicate]
    omega
  have hQle : q.eval n ≤
      q.eval (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x))).length + 1 :=
    (q.eval_mono hlen).trans (Nat.le_succ _)
  have hemit : ∀ i, ProdEval.emit F inLen q
      ((ProdEval.step inLen)^[i] (ProdEval.start (pairEncode (List.replicate n true) (List.ofFn x)))) =
      if q.eval n ≤ i then []
      else F (pairEncode (List.replicate n true)
        (((List.ofFn x).drop (i * inLen.eval n)).take (inLen.eval n))) := by
    intro i
    rw [ProdEval.iterate_step_start]
    simp [ProdEval.emit, ProdEval.u, ProdEval.cnt, ProdEval.rest]
  simp only [hemit]
  rw [flatMap_range_ite_eq_flatten_ofFn _ hQle]
  congr 2
  funext i
  rw [ofFn_block_eq_take_drop]

/-! ### The capped binary-to-unary converter -/

namespace UnaryOf

/-- The pad `1^L` of the state word `⟨pad, ⟨rest, acc⟩⟩`: the cap on the accumulator. -/
def pad (w : List Bool) : List Bool := pairFstD w

/-- The unread bits of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def rest (w : List Bool) : List Bool := pairFstD (pairSndD w)

/-- The unary accumulator of the state word `⟨pad, ⟨rest, acc⟩⟩`. -/
def acc (w : List Bool) : List Bool := pairSndD (pairSndD w)

/-- The accumulator doubled, plus the next bit: `1^{2a + bit}`. -/
def dbl (w : List Bool) : List Bool :=
  acc w ++ acc w ++ (if (rest w).headD false then [true] else [])

/-- The doubled accumulator, capped at the pad (so that the orbit of every word is bounded). -/
def capped (w : List Bool) : List Bool :=
  if (dbl w).length ≤ (pad w).length then dbl w else pad w

/-- One round: read one bit if any remain, else stay. -/
def step (w : List Bool) : List Bool :=
  if rest w = [] then w else pairEncode (pad w) (pairEncode (rest w).tail (capped w))

/-- The initial state `⟨pad, ⟨b, []⟩⟩` of the input `⟨pad, b⟩`. -/
def start (z : List Bool) : List Bool := pairEncode (pairFstD z) (pairEncode (pairSndD z) [])

/-- The pad is polynomial-time. -/
theorem pad_poly : PolyTimeComputable pad := polyTimeComputable_pairFstD

/-- The unread bits are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD

/-- The accumulator is polynomial-time. -/
theorem acc_poly : PolyTimeComputable acc :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- Doubling is polynomial-time. -/
theorem dbl_poly : PolyTimeComputable dbl := by
  have hbit : PolyTimeComputable fun w => [(rest w).headD false] :=
    StateLoop.headBit_poly.comp rest_poly
  exact (acc_poly.append acc_poly).append
    (polyTimeComputable_ite hbit (polyTimeComputable_const [true]) (polyTimeComputable_const []))

/-- Capping is polynomial-time. -/
theorem capped_poly : PolyTimeComputable capped := by
  convert polyTimeComputable_ite (StateLoop.lenLe_comp pad_poly dbl_poly) dbl_poly pad_poly using 1
  funext w
  simp [capped]

/-- The step is polynomial-time. -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_ite (StateLoop.isNil_poly.comp rest_poly) polyTimeComputable_id
    (pad_poly.pairEncode ((StateLoop.tail_poly.comp rest_poly).pairEncode capped_poly)) using 1
  funext w
  simp [step]

/-- The initial state is polynomial-time. -/
theorem start_poly : PolyTimeComputable start :=
  polyTimeComputable_pairFstD.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))

/-- The capped accumulator never exceeds the pad. -/
theorem length_capped_le (w : List Bool) : (capped w).length ≤ (pad w).length := by
  unfold capped
  split_ifs with h
  · exact h
  · exact le_rfl

/-- The unread bits of any word are no longer than the word. -/
theorem length_rest_le (w : List Bool) : (rest w).length ≤ w.length := by
  have h1 := length_pairFstD_le (pairSndD w)
  have h2 := StateLoop.length_pairFstD_add_pairSndD_le w
  unfold rest
  omega

/-- The orbit invariant on arbitrary words: the orbit point is the start word or a state word
`⟨pad w, ⟨r, a⟩⟩` with `|r| ≤ |w|` and `|a| ≤ |pad w|`. -/
def Inv (w w' : List Bool) : Prop :=
  w' = w ∨ ∃ r a : List Bool,
    w' = pairEncode (pad w) (pairEncode r a) ∧ r.length ≤ w.length ∧ a.length ≤ (pad w).length

/-- The invariant is preserved by the step. -/
theorem inv_step (w w' : List Bool) (h : Inv w w') : Inv w (step w') := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · unfold step
    split_ifs with h0
    · exact Or.inl rfl
    · refine Or.inr ⟨(rest w').tail, capped w', rfl, ?_, length_capped_le w'⟩
      have := List.length_tail (l := rest w')
      have := length_rest_le w'
      omega
  · have hpad : pad (pairEncode (pad w) (pairEncode r a)) = pad w := by simp [pad]
    have hrest : rest (pairEncode (pad w) (pairEncode r a)) = r := by simp [rest]
    unfold step
    split_ifs with h0
    · exact Or.inr ⟨r, a, rfl, hr, ha⟩
    · refine Or.inr ⟨r.tail, capped (pairEncode (pad w) (pairEncode r a)), ?_, ?_, ?_⟩
      · rw [hpad, hrest]
      · have := List.length_tail (l := r)
        omega
      · have := length_capped_le (pairEncode (pad w) (pairEncode r a))
        rwa [hpad] at this

/-- A word satisfying the invariant has length at most `5|w| + 4`. -/
theorem length_le_of_inv {w w' : List Bool} (h : Inv w w') : w'.length ≤ 5 * w.length + 4 := by
  rcases h with rfl | ⟨r, a, rfl, hr, ha⟩
  · omega
  · have := length_pairFstD_le w
    simp only [length_pairEncode, pad] at *
    omega

/-- The whole orbit satisfies the invariant. -/
theorem inv_iterate (w : List Bool) (i : ℕ) : Inv w (step^[i] w) := by
  induction i with
  | zero => exact Or.inl rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact inv_step w _ ih

/-- The orbit of every word stays within `5|w| + 4`. -/
theorem length_iterate_le (w : List Bool) (i : ℕ) : (step^[i] w).length ≤ 5 * w.length + 4 :=
  length_le_of_inv (inv_iterate w i)

/-- The orbit on a genuine input `⟨p, b⟩` with `bitListToNat b ≤ |p|`: after `i` rounds the state
is `⟨p, ⟨b.drop i, 1^{bitListToNat (b.take i)}⟩⟩`.

**Proof sketch.** Induction on `i`. While bits remain (`List.drop_eq_getElem_cons`), the step
doubles the accumulator and adds the bit `b[i]`, giving `1^{bitListToNat (b.take (i + 1))}`
(`List.take_append_getElem`, `bitListToNat_append_singleton`); the cap never fires because
`bitListToNat (b.take (i + 1)) ≤ bitListToNat b ≤ |p|` (`bitListToNat_take_le`). Once the bits are
exhausted the step is the identity and `b.take (i + 1) = b.take i`. -/
theorem iterate_start (p b : List Bool) (hb : bitListToNat b ≤ p.length) (i : ℕ) :
    step^[i] (start (pairEncode p b)) =
      pairEncode p (pairEncode (b.drop i) (List.replicate (bitListToNat (b.take i)) true)) := by
  induction i with
  | zero => simp [start, bitListToNat]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    by_cases hi : i < b.length
    · have hdrop := List.drop_eq_getElem_cons hi
      have hdbl : dbl (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        simp only [dbl, acc, rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop, List.headD_cons]
        rw [← List.take_append_getElem hi, bitListToNat_append_singleton, two_mul, List.replicate_add,
          List.replicate_add]
        cases hbi : b[i] <;> simp
      have hcap : capped (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) =
          List.replicate (bitListToNat (b.take (i + 1))) true := by
        unfold capped
        rw [hdbl, if_pos]
        rw [List.length_replicate]
        simp only [pad, pairFstD_pairEncode]
        exact (bitListToNat_take_le b (i + 1)).trans hb
      have hne : rest (pairEncode p (pairEncode (b.drop i)
          (List.replicate (bitListToNat (b.take i)) true))) ≠ [] := by
        simp only [rest, pairFstD_pairEncode, pairSndD_pairEncode, hdrop]
        exact List.cons_ne_nil _ _
      unfold step
      rw [if_neg hne, hcap]
      simp only [pad, rest, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop]
    · have hle : b.length ≤ i := not_lt.1 hi
      have h1 : b.drop i = [] := List.drop_eq_nil_of_le hle
      have h2 : b.drop (i + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h3 : b.take (i + 1) = b.take i := by
        rw [List.take_of_length_le hle, List.take_of_length_le (by omega)]
      rw [h2, h3]
      unfold step
      rw [if_pos (by simp [rest, h1]), h1]

end UnaryOf

/-- **The capped binary-to-unary converter**: a polynomial-time `U` with
`U ⟨p, b⟩ = 1^{bitListToNat b}` whenever `bitListToNat b ≤ |p|` (the pad `p` bounds the output; the
rejection sampler of Algorithm 38.5 reads each `k`-bit trial as a number below `2^k ≤ 2m`).

**Proof sketch.** `Complexity.polyTimeComputable_iterate` with `R := var` on the state word
`⟨p, ⟨rest, acc⟩⟩` (`UnaryOf`): each round doubles the unary accumulator and adds the next
bit, capped at the pad so that the orbit of every word stays within `5|w| + 4`
(`UnaryOf.length_iterate_le`); on a genuine input the cap never fires
(`UnaryOf.iterate_start`), and after `|b|` rounds the state is `⟨p, ⟨[], 1^{bitListToNat b}⟩⟩`. -/
theorem exists_unaryOf : ∃ U : List Bool → List Bool, PolyTimeComputable U ∧
    ∀ p b : List Bool, bitListToNat b ≤ p.length → U (pairEncode p b) = List.replicate (bitListToNat b) true := by
  have horbit : ∀ (w : List Bool) (i : ℕ), i ≤ PolyExpr.var.eval w.length →
      (UnaryOf.step^[i] w).length ≤ (PolyExpr.add (.mul (.const 5) .var) (.const 4)).eval w.length := by
    intro w i _
    simpa using UnaryOf.length_iterate_le w i
  have hiter := polyTimeComputable_iterate UnaryOf.step_poly .var _ horbit
  refine ⟨_, UnaryOf.acc_poly.comp (hiter.comp UnaryOf.start_poly), fun p b hb => ?_⟩
  simp only [Function.comp_apply, PolyExpr.eval_var]
  rw [UnaryOf.iterate_start p b hb]
  have hlen : b.length ≤ (UnaryOf.start (pairEncode p b)).length := by
    simp only [UnaryOf.start, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_nil]
    omega
  rw [List.drop_eq_nil_of_le hlen, List.take_of_length_le hlen]
  simp [UnaryOf.acc]

/-! ### The rejection sampler of the position -/

namespace PosLoop

/-- The trial length `1^k` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def ukk (v : List Bool) : List Bool := pairFstD (pairFstD v)

/-- The range `1^m` of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def uM (v : List Bool) : List Bool := pairSndD (pairFstD v)

/-- The unread trials of the state word `⟨⟨1^k, 1^m⟩, rest⟩`. -/
def rest (v : List Bool) : List Bool := pairSndD v

/-- One round: drop one trial of `k` bits. -/
def step (v : List Bool) : List Bool := pairEncode (pairFstD v) ((rest v).drop (ukk v).length)

/-- The current trial: the next `k` bits. -/
def trial (v : List Bool) : List Bool := (rest v).take (ukk v).length

/-- The current trial as a unary number, through the converter `U` with pad `1^{2m}`. -/
def unum (U : List Bool → List Bool) (v : List Bool) : List Bool :=
  U (pairEncode (uM v ++ uM v) (trial v))

/-- The acceptance test: a full trial remains and its value is below `m`. -/
def acc (U : List Bool → List Bool) (v : List Bool) : Bool :=
  decide ((ukk v).length ≤ (rest v).length) && !decide ((uM v).length ≤ (unum U v).length)

/-- The trial length is polynomial-time. -/
theorem ukk_poly : PolyTimeComputable ukk := polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD

/-- The range is polynomial-time. -/
theorem uM_poly : PolyTimeComputable uM := polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD

/-- The unread trials are polynomial-time. -/
theorem rest_poly : PolyTimeComputable rest := polyTimeComputable_pairSndD

/-- The step is polynomial-time (`Complexity.polyTimeComputable_pairDropPoly` at `var`). -/
theorem step_poly : PolyTimeComputable step := by
  convert polyTimeComputable_pairFstD.pairEncode
    ((polyTimeComputable_pairDropPoly .var).comp (ukk_poly.pairEncode rest_poly)) using 1
  funext v
  simp [step]

/-- The current trial is polynomial-time (`Complexity.polyTimeComputable_pairTakePoly` at `var`). -/
theorem trial_poly : PolyTimeComputable trial := by
  convert (polyTimeComputable_pairTakePoly .var).comp (ukk_poly.pairEncode rest_poly) using 1
  funext v
  simp [trial]

/-- The unary value of the trial is polynomial-time. -/
theorem unum_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable (unum U) :=
  hU.comp ((uM_poly.append uM_poly).pairEncode trial_poly)

/-- The acceptance test is polynomial-time. -/
theorem acc_poly {U : List Bool → List Bool} (hU : PolyTimeComputable U) :
    PolyTimeComputable fun v => [acc U v] :=
  polyTimeComputable_and (StateLoop.lenLe_comp rest_poly ukk_poly)
    (StateLoop.not_poly (StateLoop.lenLe_comp (unum_poly hU) uM_poly))

/-- Re-pairing the first component of a word with a shorter second component does not lengthen a
pair, and gives a word of length `2` on a non-pair. -/
theorem length_pairEncode_pairFstD_le (v s : List Bool) (hs : s.length ≤ (pairSndD v).length) :
    (pairEncode (pairFstD v) s).length ≤ max v.length 2 := by
  cases hv : pairDecode v with
  | none =>
    simp only [pairFstD, pairSndD, hv, Option.map_none, Option.getD_none, List.length_nil,
      nonpos_iff_eq_zero, List.length_eq_zero_iff] at hs ⊢
    subst hs
    simp [length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have := eq_pairEncode_of_pairDecode v a b hv
    subst this
    simp only [pairFstD_pairEncode, pairSndD_pairEncode] at hs ⊢
    rw [length_pairEncode, length_pairEncode]
    omega

/-- The orbit of every word stays within `|v| + 2`. -/
theorem length_iterate_le (v : List Bool) (t : ℕ) : (step^[t] v).length ≤ v.length + 2 := by
  have key : ∀ t, (step^[t] v).length ≤ max v.length 2 := by
    intro t
    induction t with
    | zero => exact le_max_left _ _
    | succ t ih =>
      rw [Function.iterate_succ_apply']
      refine (length_pairEncode_pairFstD_le _ _
        (by rw [List.length_drop]; exact Nat.sub_le _ _)).trans ?_
      exact max_le (ih.trans (le_refl _)) (le_max_right _ _)
  exact (key t).trans (by omega)

/-- The orbit on a genuine input: after `t` rounds, `t` trials have been dropped. -/
theorem iterate_step_start (kk M : ℕ) (L : List Bool) (t : ℕ) :
    step^[t] (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) L) =
      pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (L.drop (t * kk)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [step, rest, ukk, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
      List.drop_drop]
    congr 2
    ring

end PosLoop

/-- A trial succeeds iff its value is below `m`. -/
theorem isSome_uniformFromBits {m k : ℕ} (b : Fin k → Bool) :
    (uniformFromBits m k b).isSome = decide (bitsToNat b < m) := by
  unfold uniformFromBits
  split_ifs with h <;> simp [h]

/-- **The position sampler** [PS10, Algorithm 38.5, "`i ← [m]`", by rejection (D10)]: a
polynomial-time `Pm` with `Pm ⟨⟨1^k, 1^m⟩, trials⟩ = 1^i` where `i` is the output of
`rejectionSample m k n` on the `n` trials of `k` bits encoded in `trials` (`0` on failure),
for `0 < m`, `0 < k` and `2^k ≤ 2m`.

**Proof sketch.** `Complexity.polyTimeComputable_iterateFind` with `R := var` on the state word
`⟨⟨1^k, 1^m⟩, rest⟩` (`PosLoop`): each round drops one trial; the test accepts when a full
trial remains and its unary value (`exists_unaryOf` with pad `1^{2m}`, valid since the value is
below `2^k ≤ 2m`) is shorter than `1^m`; the payload is that unary value. The orbit of every
word is bounded by `|v| + 2` (`PosLoop.length_iterate_le`). On a genuine input the test at
round `t < n` is `bitsToNat (trial t) < m` and fails from round `n` on (no full trial remains),
so the loop's `find?` is the `find?` over `finRange n` (`find?_range_eq_map_find?_finRange`),
which is the `findSome?` of `rejectionSample` (`findSome?_eq_bind_find?`,
`isSome_uniformFromBits`). -/
theorem exists_posMachine : ∃ Pm : List Bool → List Bool, PolyTimeComputable Pm ∧
    ∀ (M kk n : ℕ) (hM : 0 < M), 0 < kk → 2 ^ kk ≤ 2 * M → ∀ pb' : Fin (n * kk) → Bool,
      Pm (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')) =
        List.replicate
          ((rejectionSample M kk n fun t j => pb' (finProdFinEquiv (t, j))).getD ⟨0, hM⟩).val true := by
  obtain ⟨U, hU, hUspec⟩ := exists_unaryOf
  have horbit : ∀ (v : List Bool) (t : ℕ), t ≤ PolyExpr.var.eval v.length →
      (PosLoop.step^[t] v).length ≤ (PolyExpr.add .var (.const 2)).eval v.length := by
    intro v t _
    simpa using PosLoop.length_iterate_le v t
  have hfind := polyTimeComputable_iterateFind PosLoop.step_poly (PosLoop.acc_poly hU)
    (PosLoop.unum_poly hU) .var _ horbit
  refine ⟨_, hfind, fun M kk n hM hkk h2 pb' => ?_⟩
  have hunum : ∀ t : Fin n, PosLoop.unum U (PosLoop.step^[(t : ℕ)]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      List.replicate (bitsToNat fun j => pb' (finProdFinEquiv (t, j))) true := by
    intro t
    rw [PosLoop.iterate_step_start]
    simp only [PosLoop.unum, PosLoop.uM, PosLoop.trial, PosLoop.rest, PosLoop.ukk,
      pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
    rw [← ofFn_block_eq_take_drop pb' t, hUspec]
    · rfl
    · rw [List.length_append, List.length_replicate]
      have := bitsToNat_lt fun j => pb' (finProdFinEquiv (t, j))
      rw [bitsToNat_eq_bitListToNat] at this
      omega
  have hacc : ∀ t : ℕ, PosLoop.acc U (PosLoop.step^[t]
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb'))) =
      if h : t < n then decide (bitsToNat (fun j => pb' (finProdFinEquiv (⟨t, h⟩, j))) < M)
      else false := by
    intro t
    split_ifs with h
    · have := hunum ⟨t, h⟩
      simp only at this
      unfold PosLoop.acc
      rw [this, PosLoop.iterate_step_start]
      simp only [PosLoop.ukk, PosLoop.uM, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.length_drop, List.length_ofFn]
      have hmul : (t + 1) * kk ≤ n * kk := Nat.mul_le_mul_right kk h
      rw [Nat.add_mul, Nat.one_mul] at hmul
      have h1 : kk ≤ n * kk - t * kk := by omega
      simp [h1, ← decide_not]
    · unfold PosLoop.acc
      rw [PosLoop.iterate_step_start]
      have hmul : n * kk ≤ t * kk := Nat.mul_le_mul_right kk (not_lt.1 h)
      simp only [PosLoop.ukk, PosLoop.rest, pairFstD_pairEncode, pairSndD_pairEncode,
        List.length_replicate, List.drop_eq_nil_of_le (List.length_ofFn.trans_le hmul),
        List.length_nil]
      simp [Nat.pos_iff_ne_zero.1 hkk]
  have hR : n ≤ PolyExpr.var.eval
      (pairEncode (pairEncode (List.replicate kk true) (List.replicate M true)) (List.ofFn pb')).length + 1 := by
    have := Nat.le_mul_of_pos_right n hkk
    simp only [PolyExpr.eval_var, length_pairEncode, List.length_replicate, List.length_ofFn]
    omega
  rw [find?_range_eq_map_find?_finRange hR
    (fun t : Fin n => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)) _
    (fun t h => by rw [hacc, dif_pos h]) (fun t h => by rw [hacc, dif_neg (not_lt.2 h)])]
  have hrs : rejectionSample M kk n (fun t j => pb' (finProdFinEquiv (t, j))) =
      ((List.finRange n).find? fun t => decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M)).bind
        fun t => uniformFromBits M kk fun j => pb' (finProdFinEquiv (t, j)) := by
    unfold rejectionSample
    rw [findSome?_eq_bind_find?]
    congr 2
    funext t
    exact isSome_uniformFromBits _
  rw [hrs]
  cases hf : (List.finRange n).find? fun t =>
      decide (bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M) with
  | none => simp
  | some t =>
    have ht : bitsToNat (fun j => pb' (finProdFinEquiv (t, j))) < M := by
      simpa using List.find?_some hf
    simp only [Option.map_some, Option.bind_some]
    rw [hunum]
    unfold uniformFromBits
    rw [dif_pos ht]
    rfl

end TCSlib.Cryptography.OneWay
