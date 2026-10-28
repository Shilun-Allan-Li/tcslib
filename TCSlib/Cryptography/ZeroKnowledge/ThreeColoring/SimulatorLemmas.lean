/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Protocol

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for the 3-colouring simulator

The probability bookkeeping behind the zero-knowledge half of [PS10, Proposition 127.6]
(`ThreeColoring/Simulator.lean`): uniform indices hitting a fixed target, the first success of
a sequence of attempts, independent coordinates, and the two coin involutions of the hybrid
argument of [PS10, Proposition 128.8] — planting a fresh `(e', π)` into one attempt's coins
and merging a fresh randomness into one attempt's commitment randomness at the two endpoints
of an edge leave the coins uniform. None of these lemmas mentions the simulator itself; they
are stated for the coin layout `((e', π), r), ρ)` of one attempt (`ColSimLemmas.AttemptCoins`)
and for arbitrary events on tuples of attempts.

## Main definitions

* `TCSlib.Cryptography.ColSimLemmas.AttemptCoins` — the coin type of one attempt.
* `TCSlib.Cryptography.ColSimLemmas.mergeAt` — a randomness vector read from one source at
  the endpoints of an edge and from another elsewhere.
* `TCSlib.Cryptography.ColSimLemmas.plantEP`, `swapEP`, `swapR` — the planting map and the
  two coin involutions.

## Main results

* `TCSlib.Cryptography.ColSimLemmas.uprob_ne_idx`, `uprob_eq_idx_and` — a uniform index
  misses or hits a fixed in-range target with probability `1 - 1/m`, `1/m`.
* `TCSlib.Cryptography.ColSimLemmas.findSome?_finRange_cons_of_some`,
  `findSome?_finRange_cons_of_none` — the first success of `N + 1` attempts.
* `TCSlib.Cryptography.ColSimLemmas.uprob_and_add_uprob_not_and`, `uprob_prod_and` —
  splitting an event and independent coordinates.
* `TCSlib.Cryptography.ColSimLemmas.uprob_plantEP`, `uprob_mergeAt` — the two coin
  involutions preserve the uniform law.
* `TCSlib.Cryptography.ColSimLemmas.msgAt_multiCom` — the `i`-th message of a commitment
  vector.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Proposition 128.8.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (hybrid arguments at the concrete layer).
-/

namespace TCSlib.Cryptography.ColSimLemmas

open Complexity Turing Finset TCSlib.Cryptography

/-! ### Uniform indices -/

/-- A uniform index `b ∈ [m]` misses a fixed in-range target `f a` with probability `1 - 1/m`,
for every value of the independent coordinate `a` (`uprob_prod`, `uprob_not`,
`OneWay.uprob_eq_one_div_card`). -/
theorem uprob_ne_idx {m : ℕ} (hm : 0 < m) {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℕ) (hf : ∀ a, f a < m) :
    uprob (fun z : α × Fin m => ¬ f z.1 = (z.2 : ℕ)) = 1 - 1 / (m : ℝ) := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [uprob_prod]
  have h : ∀ a : α, uprob (fun b : Fin m => ¬ f a = (b : ℕ)) = 1 - 1 / (m : ℝ) := by
    intro a
    rw [uprob_not]
    have : (fun b : Fin m => f a = (b : ℕ)) = fun b : Fin m => b = ⟨f a, hf a⟩ := by
      funext b
      exact propext ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    rw [this, OneWay.uprob_eq_one_div_card, Fintype.card_fin]
  rw [show (fun a : α => uprob (fun b : Fin m => ¬ f a = (b : ℕ))) = fun _ => 1 - 1 / (m : ℝ)
    from funext h, OneWay.uexp_const]

/-- A uniform index `b ∈ [m]` hits the in-range target `f a` and the independent coordinate
`a` lies in `T` with probability `(1/m) · Pr[T]` (`uprob_prod`, `OneWay.uexp_indicator`). -/
theorem uprob_eq_idx_and {m : ℕ} (hm : 0 < m) {α : Type*} [Fintype α]
    (f : α → ℕ) (hf : ∀ a, f a < m) (T : α → Prop) :
    uprob (fun z : α × Fin m => f z.1 = (z.2 : ℕ) ∧ T z.1) = 1 / (m : ℝ) * uprob T := by
  classical
  have _ := hm
  rw [uprob_prod, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases hT : T a
  · simp only [hT, and_true, if_true]
    have : (fun b : Fin m => f a = (b : ℕ)) = fun b : Fin m => b = ⟨f a, hf a⟩ := by
      funext b
      exact propext ⟨fun h => Fin.ext h.symm, fun h => by rw [h]⟩
    rw [this, OneWay.uprob_eq_one_div_card, Fintype.card_fin]
  · simp only [hT, and_false, if_false, uprob_false]

/-! ### The coins of one attempt -/

/-- The coins of one attempt of the simulators of [PS10, Algorithm 128.7]: the guessed edge
index, the colour permutation, the commitment randomness and the coins of `V*`. -/
abbrev AttemptCoins (m : ℕ) (R τ : Type*) : Type _ := ((Fin m × Equiv.Perm (Fin 3)) × R) × τ

/-- The coin reindexing `(((e', π), r), ρ) ↦ (((π, r), ρ), e')` of one attempt: the guessed
edge becomes the last, independent coordinate. -/
def attemptCoinsEquiv (m : ℕ) (R ρ : Type*) :
    AttemptCoins m R ρ ≃ ((Equiv.Perm (Fin 3) × R) × ρ) × Fin m where
  toFun w := (((w.1.1.2, w.1.2), w.2), w.1.1.1)
  invFun z := (((z.2, z.1.1.1), z.1.1.2), z.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The first success of a sequence of attempts -/

/-- `List.findSome?` over `List.finRange (N + 1)` on `Fin.cons a w` with a successful head
attempt returns its value (`List.finRange_succ`, `List.findSome?_cons_of_isSome`). -/
theorem findSome?_finRange_cons_of_some {α β : Type*} {N : ℕ} (F : β → Option α) {a : β}
    (w : Fin N → β) {v : α} (ha : F a = some v) :
    (List.finRange (N + 1)).findSome? (fun t => F ((Fin.cons a w : Fin (N + 1) → β) t)) =
      some v := by
  rw [List.finRange_succ, List.findSome?_cons_of_isSome]
  · simp [ha]
  · simp [ha]

/-- `List.findSome?` over `List.finRange (N + 1)` on `Fin.cons a w` with a failed head attempt
is the search over the tail (`List.findSome?_cons_of_isNone`, `List.findSome?_map`). -/
theorem findSome?_finRange_cons_of_none {α β : Type*} {N : ℕ} (F : β → Option α) {a : β}
    (w : Fin N → β) (ha : F a = none) :
    (List.finRange (N + 1)).findSome? (fun t => F ((Fin.cons a w : Fin (N + 1) → β) t)) =
      (List.finRange N).findSome? fun t => F (w t) := by
  rw [List.finRange_succ, List.findSome?_cons_of_isNone, List.findSome?_map]
  · simp only [Function.comp_def, Fin.cons_succ]
  · simp [ha]

/-- Splitting an event along a second event: `Pr[p ∧ q] + Pr[¬p ∧ q] = Pr[q]`. -/
theorem uprob_and_add_uprob_not_and {α : Type*} [Fintype α] (p q : α → Prop) :
    uprob (fun a => p a ∧ q a) + uprob (fun a => ¬ p a ∧ q a) = uprob q := by
  classical
  simp only [uprob_eq_card_filter]
  rw [← add_div]
  congr 1
  have h := filter_card_add_filter_neg_card_eq_card (s := univ.filter q) p
  rw [filter_filter, filter_filter] at h
  norm_cast
  rw [← h]
  congr 2 <;> ext a <;> simp [and_comm]

/-- Independent coordinates: `Pr[A(z.1) ∧ B(z.2)] = Pr[A] · Pr[B]` on a product
(`uprob_prod`, `OneWay.uexp_indicator`). -/
theorem uprob_prod_and {α β : Type*} [Fintype α] [Fintype β] (A : α → Prop) (B : β → Prop) :
    uprob (fun z : α × β => A z.1 ∧ B z.2) = uprob A * uprob B := by
  classical
  rw [uprob_prod, mul_comm, ← OneWay.uexp_indicator]
  congr 1
  funext a
  by_cases ha : A a
  · simp [ha]
  · simp [ha, uprob_false]

/-! ### Merged randomness -/

/-- The randomness `a` at the endpoints of `p`, `b` elsewhere (the randomness of the planted
attempt's commitment vector in the hybrid argument of [PS10, Proposition 128.8]: the
reduction's own at the endpoints of the guessed edge, the challenger's elsewhere). -/
def mergeAt {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    Fin m → Fin ℓ → Bool :=
  fun i => if i = p.1 ∨ i = p.2 then a i else b i

/-- `mergeAt` at the first endpoint. -/
theorem mergeAt_fst {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    mergeAt p a b p.1 = a p.1 := by
  simp [mergeAt]

/-- `mergeAt` at the second endpoint. -/
theorem mergeAt_snd {m ℓ : ℕ} (p : Fin m × Fin m) (a b : Fin m → Fin ℓ → Bool) :
    mergeAt p a b p.2 = a p.2 := by
  simp [mergeAt]

/-- Merging twice on the left. -/
theorem mergeAt_mergeAt_left {m ℓ : ℕ} (p : Fin m × Fin m) (a b c : Fin m → Fin ℓ → Bool) :
    mergeAt p (mergeAt p a b) c = mergeAt p a c := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- Merging twice on the right. -/
theorem mergeAt_mergeAt_right {m ℓ : ℕ} (p : Fin m × Fin m) (a b c : Fin m → Fin ℓ → Bool) :
    mergeAt p a (mergeAt p b c) = mergeAt p a c := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- Merging a function with itself. -/
theorem mergeAt_self {m ℓ : ℕ} (p : Fin m × Fin m) (a : Fin m → Fin ℓ → Bool) :
    mergeAt p a a = a := by
  funext i
  simp only [mergeAt]
  split_ifs <;> rfl

/-- The `i`-th message of the commitment vector `multiCom Com v r` is `Com ⟨v i, r i⟩`
(`msgAt_encodeMsgs`, `List.getElem_ofFn`). -/
theorem msgAt_multiCom (Com : List Bool → List Bool) {q n ℓ : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin ℓ → Bool) (i : Fin q) :
    msgAt (multiCom Com v r) i = Com (pairEncode (List.ofFn (v i)) (List.ofFn (r i))) := by
  rw [multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The two coin involutions of the hybrid argument -/

section Involutions

variable {m : ℕ} {R τ : Type*}

/-- Replacing the `(e', π)` part of an attempt's coins. -/
def plantEP (ep : Fin m × Equiv.Perm (Fin 3)) (w : AttemptCoins m R τ) : AttemptCoins m R τ :=
  ((ep, w.1.2), w.2)

/-- The involution exchanging the external `(e', π)` with the one of attempt `k`. -/
def swapEP {N : ℕ} (k : Fin N) (ρ' : Type*) :
    (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') ≃
      (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') where
  toFun y := ((y.2.1 k).1.1, (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2))
  invFun y := ((y.2.1 k).1.1, (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2))
  left_inv y := by
    rcases y with ⟨ep, w, r⟩
    simp only [Function.update_self, plantEP, Function.update_idem, Prod.mk.eta,
      Function.update_eq_self]
  right_inv y := by
    rcases y with ⟨ep, w, r⟩
    simp only [Function.update_self, plantEP, Function.update_idem, Prod.mk.eta,
      Function.update_eq_self]

/-- **Planting a uniform `(e', π)` at attempt `k` leaves the coins uniform**: the law of the
tuple with attempt `k`'s `(e', π)` replaced by an independent uniform one is the law of the
tuple (`swapEP` is a bijection, `uprob_comp_equiv`, `uprob_fst`). -/
theorem uprob_plantEP (hm : 0 < m) [Fintype R] [Fintype τ] {N : ℕ} (k : Fin N) {ρ' : Type*}
    [Fintype ρ'] (P : (Fin N → AttemptCoins m R τ) × ρ' → Prop) :
    uprob (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2)) = uprob P := by
  haveI : Nonempty (Fin m × Equiv.Perm (Fin 3)) := ⟨(⟨0, hm⟩, 1)⟩
  have h := uprob_comp_equiv (swapEP (m := m) (R := R) (τ := τ) k ρ')
    (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') => P y.2)
  rw [show (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') =>
      P (swapEP (m := m) (R := R) (τ := τ) k ρ' y).2) = fun y =>
      P (Function.update y.2.1 k (plantEP y.1 (y.2.1 k)), y.2.2) from rfl] at h
  rw [h, ← uprob_comp_equiv (Equiv.prodComm _ _)
    (fun y : (Fin m × Equiv.Perm (Fin 3)) × ((Fin N → AttemptCoins m R τ) × ρ') => P y.2)]
  exact uprob_fst P

end Involutions

section MergeInvolution

variable {m n ℓ : ℕ} {τ : Type*}

/-- The involution exchanging the challenger's randomness with attempt `k`'s randomness off
the endpoints of `p`. -/
def swapR {N : ℕ} (k : Fin N) (p : Fin n × Fin n) (ρ' : Type*) :
    (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') ≃
      (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') where
  toFun y := (mergeAt p y.1 (y.2.1 k).1.2,
    (Function.update y.2.1 k (((y.2.1 k).1.1, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2))
  invFun y := (mergeAt p y.1 (y.2.1 k).1.2,
    (Function.update y.2.1 k (((y.2.1 k).1.1, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2))
  left_inv y := by
    rcases y with ⟨r', w, r⟩
    simp only [Function.update_self, Function.update_idem, mergeAt_mergeAt_left,
      mergeAt_mergeAt_right, mergeAt_self, Prod.mk.eta, Function.update_eq_self]
  right_inv y := by
    rcases y with ⟨r', w, r⟩
    simp only [Function.update_self, Function.update_idem, mergeAt_mergeAt_left,
      mergeAt_mergeAt_right, mergeAt_self, Prod.mk.eta, Function.update_eq_self]

/-- **Merging a fresh uniform randomness into attempt `k` leaves the coins uniform**: the law
of the tuple with attempt `k` replaced by `((ep, mergeAt p r_k r'), ρ_k)` for an independent
uniform `r'` is the law of the tuple with attempt `k` replaced by `((ep, r_k), ρ_k)`.

**Proof sketch.** Reindex the coins by the involution `swapR` (`uprob_comp_equiv`), which
exchanges `r'` and `r_k` off the endpoints of `p` and leaves the planted tuple invariant
(`Function.update_self`, `Function.update_idem`); the event then no longer depends on the
first coordinate, which `uprob_fst` removes. -/
theorem uprob_mergeAt [Fintype τ] {N : ℕ} (k : Fin N) (p : Fin n × Fin n)
    (ep : Fin m × Equiv.Perm (Fin 3)) {ρ' : Type*} [Fintype ρ']
    (P : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' → Prop) :
    uprob (fun y : (Fin n → Fin ℓ → Bool) ×
        ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
        P (Function.update y.2.1 k ((ep, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2), y.2.2)) =
      uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
        P (Function.update z.1 k (plantEP ep (z.1 k)), z.2)) := by
  have h := uprob_comp_equiv (swapR (m := m) (τ := τ) k p ρ')
    (fun y : (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP ep (y.2.1 k)), y.2.2))
  have hfun : (fun y : (Fin n → Fin ℓ → Bool) ×
      ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update (swapR (m := m) (τ := τ) k p ρ' y).2.1 k
        (plantEP ep ((swapR (m := m) (τ := τ) k p ρ' y).2.1 k)),
        (swapR (m := m) (τ := τ) k p ρ' y).2.2)) =
      fun y => P (Function.update y.2.1 k ((ep, mergeAt p (y.2.1 k).1.2 y.1), (y.2.1 k).2),
        y.2.2) := by
    funext y
    rcases y with ⟨r', w, r⟩
    simp only [swapR, plantEP, Equiv.coe_fn_mk, Function.update_self, Function.update_idem]
  rw [hfun] at h
  rw [h, ← uprob_comp_equiv (Equiv.prodComm _ _)
    (fun y : (Fin n → Fin ℓ → Bool) × ((Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ') =>
      P (Function.update y.2.1 k (plantEP ep (y.2.1 k)), y.2.2))]
  exact uprob_fst (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
    P (Function.update z.1 k (plantEP ep (z.1 k)), z.2))

end MergeInvolution

/-! ### Truncated attempts: the first success of `N` independent attempts -/

section Truncation

variable {W U α : Type*} [Fintype W] [Fintype U]

/-- The first success among `N` independent attempts `att (w t)` (`none` if all fail): the
common shape of the truncated simulators `colSimTrunc`, `colSimTruncW`, `colSimTruncH`. -/
def truncAttempts (att : W → Option α) (N : ℕ) (w : Fin N → W) : Option α :=
  (List.finRange N).findSome? fun t => att (w t)

/-- One step of the recursion for the law of the truncated attempts: if one attempt fails with
probability `θ` and succeeds with a value in `T` with probability `(1 - θ) · Pr[T(view)]`, then
`Pr[T(S_{N+1})] = θ · Pr[T(S_N)] + (1 - θ) · Pr[T(some view)]`.

**Proof sketch.** Split the coins of the `N + 1` attempts as (first attempt, remaining
attempts) by `Fin.consEquiv` (`uprob_comp_equiv`) and the event along "the first attempt
fails" (`uprob_and_add_uprob_not_and`): when it fails, `S_{N+1}` is `S_N` on the remaining
coins (`findSome?_finRange_cons_of_none`), and the two factors are independent
(`uprob_prod_and`); when it succeeds the output is its value
(`findSome?_finRange_cons_of_some`), an event of the first coordinate alone (`uprob_fst`). -/
theorem uprob_truncAttempts_succ [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) (T : Option α → Prop) :
    uprob (fun w : Fin (N + 1) → W => T (truncAttempts att (N + 1) w)) =
      θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) +
        (1 - θ) * uprob (fun u => T (some (view u))) := by
  rw [← uprob_comp_equiv (Fin.consEquiv fun _ : Fin (N + 1) => W)]
  have hsplit := uprob_and_add_uprob_not_and
    (fun z : W × (Fin N → W) => att z.1 = none)
    (fun z => T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z)))
  have hA : uprob (fun z : W × (Fin N → W) => att z.1 = none ∧
        T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z))) =
      θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) := by
    rw [← hnone, ← uprob_prod_and (fun a : W => att a = none)
      (fun w : Fin N → W => T (truncAttempts att N w))]
    refine OneWay.uprob_congr fun z => and_congr_right fun hz => ?_
    rw [show (Fin.consEquiv fun _ : Fin (N + 1) => W) z = Fin.cons z.1 z.2 from rfl]
    unfold truncAttempts
    rw [findSome?_finRange_cons_of_none _ _ hz]
  have hB : uprob (fun z : W × (Fin N → W) => ¬ att z.1 = none ∧
        T (truncAttempts att (N + 1) ((Fin.consEquiv fun _ => W) z))) =
      (1 - θ) * uprob (fun u => T (some (view u))) := by
    rw [← hsome (fun v => T (some v)),
      ← uprob_fst (β := Fin N → W) (fun a : W => ∃ v, att a = some v ∧ T (some v))]
    refine OneWay.uprob_congr fun z => ?_
    rw [show (Fin.consEquiv fun _ : Fin (N + 1) => W) z = Fin.cons z.1 z.2 from rfl]
    unfold truncAttempts
    constructor
    · rintro ⟨hne, hT⟩
      obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 hne
      exact ⟨v, hv, by rwa [findSome?_finRange_cons_of_some _ _ hv] at hT⟩
    · rintro ⟨v, hv, hT⟩
      exact ⟨by simp [hv], by rwa [findSome?_finRange_cons_of_some _ _ hv]⟩
  rw [← hsplit, hA, hB]

/-- The distance between the law of the truncated attempts and the law of `some view` shrinks
by the factor `θ` with every attempt: `|Pr[T(S_N)] - Pr[T(some view)]| ≤ θ^N`.

**Proof sketch.** Induction on `N`. For `N = 0` the output is `none` and both probabilities
lie in `[0, 1]`. The step is `uprob_truncAttempts_succ`:
`Pr[T(S_{N+1})] - p = θ (Pr[T(S_N)] - p)`. -/
theorem abs_uprob_truncAttempts_sub_le [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hθ : 0 ≤ θ) (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) (T : Option α → Prop) :
    |uprob (fun w : Fin N → W => T (truncAttempts att N w)) -
      uprob (fun u => T (some (view u)))| ≤ θ ^ N := by
  induction N with
  | zero =>
    have h0 : ∀ w : Fin 0 → W, truncAttempts att 0 w = none := fun w => by
      simp [truncAttempts]
    have hp0 := uprob_nonneg fun u => T (some (view u))
    have hp1 := uprob_le_one fun u => T (some (view u))
    simp only [h0, pow_zero]
    by_cases hT : T none
    · simp only [hT, uprob_true]
      rw [abs_le]
      constructor <;> linarith
    · simp only [hT, uprob_false]
      rw [abs_le]
      constructor <;> linarith
  | succ N ih =>
    rw [uprob_truncAttempts_succ att view hnone hsome N T]
    have h : θ * uprob (fun w : Fin N → W => T (truncAttempts att N w)) +
        (1 - θ) * uprob (fun u => T (some (view u))) - uprob (fun u => T (some (view u))) =
        θ * (uprob (fun w : Fin N → W => T (truncAttempts att N w)) -
          uprob (fun u => T (some (view u)))) := by ring
    rw [h, abs_mul, abs_of_nonneg hθ, pow_succ, mul_comm]
    exact mul_le_mul_of_nonneg_right ih hθ

/-- **Truncated attempts are statistically `θ^N`-close to the ideal output** when one attempt
fails with probability `θ` and, conditioned on success, has exactly the law of the ideal
output (`abs_uprob_truncAttempts_sub_le`). -/
theorem statClose_truncAttempts [Nonempty W] (att : W → Option α) (view : U → α) {θ : ℝ}
    (hθ : 0 ≤ θ) (hnone : uprob (fun w => att w = none) = θ)
    (hsome : ∀ T : α → Prop, uprob (fun w => ∃ v, att w = some v ∧ T v) =
      (1 - θ) * uprob (fun u => T (view u)))
    (N : ℕ) :
    StatClose (truncAttempts att N) (fun u => some (view u)) (θ ^ N) :=
  fun T => abs_uprob_truncAttempts_sub_le att view hθ hnone hsome N T

end Truncation

/-! ### The hybrid argument over the attempts -/

section Hybrid

variable {W α ρ' : Type*}

/-- The `k`-th standard hybrid: attempts `< k` of type `H`, the others of type `Wa`
(the shape of `colSimHyb`). -/
def hybStd (H Wa : W → Option α) (N k : ℕ) (w : Fin N → W) : Option α :=
  (List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (w t) else Wa (w t)

/-- The hybrid with an arbitrary attempt `A` at position `k`: attempts `< k` are of type `H`,
attempt `k` is `A`, the later attempts are of type `Wa`; `D` judges the first success
(the shape of `colSimRed`, with `A` the planted attempt). -/
def hybGen (H Wa : W → Option α) {N : ℕ} (k : Fin N) (A : W → Option α)
    (D : Option α → ρ' → Bool) (z : (Fin N → W) × ρ') : Bool :=
  D ((List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then H (z.1 t)
    else if t = k then A (z.1 t) else Wa (z.1 t)) z.2

/-- Replacing attempt `k`'s coins and its attempt function consistently leaves the hybrid
unchanged. -/
theorem hybGen_update (H Wa : W → Option α) {N : ℕ} (k : Fin N) {A A' : W → Option α}
    (D : Option α → ρ' → Bool) {w : Fin N → W} {w' : W} (h : A (w k) = A' w') (r : ρ') :
    hybGen H Wa k A D (w, r) = hybGen H Wa k A' D (Function.update w k w', r) := by
  unfold hybGen
  congr 2
  funext t
  by_cases ht : t = k
  · subst ht
    simp only [Function.update_self, lt_irrefl, if_false, if_true, h]
  · simp only [Function.update_of_ne ht, ht, if_false]

/-- The `k`-th standard hybrid is the generic hybrid with a `Wa` attempt at `k`. -/
theorem hybGen_W (H Wa : W → Option α) {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    (w : Fin N → W) (r : ρ') :
    D (hybStd H Wa N k w) r = hybGen H Wa k Wa D (w, r) := by
  unfold hybGen hybStd
  congr 2
  funext t
  split_ifs <;> rfl

/-- The `(k+1)`-th standard hybrid is the generic hybrid with an `H` attempt at `k`. -/
theorem hybGen_H (H Wa : W → Option α) {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    (w : Fin N → W) (r : ρ') :
    D (hybStd H Wa N (k + 1) w) r = hybGen H Wa k H D (w, r) := by
  unfold hybGen hybStd
  congr 2
  funext t
  by_cases h1 : (t : ℕ) < k
  · rw [if_pos (Nat.lt_succ_of_lt h1), if_pos h1]
  · rw [if_neg h1]
    by_cases h2 : t = k
    · rw [if_pos h2, if_pos (by rw [h2]; exact Nat.lt_succ_self _)]
    · have h3 : ¬ (t : ℕ) < k + 1 := fun h => h2 (Fin.ext (by omega))
      rw [if_neg h2, if_neg h3]

end Hybrid

section HybridCoins

variable {m n ℓ : ℕ} {τ α ρ' : Type*} [Fintype τ] [Fintype ρ']

/-- The acceptance probability of `D` on the generic hybrid with attempt `k`'s `(e', π)` fixed
to `ep`. -/
noncomputable def hybAcc (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) {N : ℕ}
    (k : Fin N) (A : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    (D : Option α → ρ' → Bool) (ep : Fin m × Equiv.Perm (Fin 3)) : ℝ :=
  uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
    hybGen H Wa k A D (Function.update z.1 k (plantEP ep (z.1 k)), z.2) = true)

/-- The acceptance probability of `D` on a generic hybrid is the average over attempt `k`'s
`(e', π)` of the fixed-`(e', π)` acceptance probabilities (`uprob_plantEP`, `uprob_prod`). -/
theorem uprob_hybGen_eq_uexp (hm : 0 < m)
    (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) {N : ℕ} (k : Fin N)
    (A : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) (D : Option α → ρ' → Bool) :
    uprob (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
        hybGen H Wa k A D z = true) =
      uexp (hybAcc H Wa k A D) := by
  rw [← uprob_plantEP hm k
    (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
      hybGen H Wa k A D z = true), uprob_prod]
  rfl

/-- A reduction that plants a challenge `cv` into attempt `k` accepts, on challenges that
make the planted attempt an `A'` attempt with merged randomness, with the fixed-`ep`
acceptance probability of the `A'` hybrid (`hybGen_update`, `uprob_mergeAt`). -/
theorem acceptProb_hybGen_planted (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    {N : ℕ} (k : Fin N) (D : Option α → ρ' → Bool)
    {Pl : List Bool → AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α}
    {X : (Fin n → Fin ℓ → Bool) → List Bool}
    {A' : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α} (p : Fin n × Fin n)
    (ep : Fin m × Equiv.Perm (Fin 3))
    (hPl : ∀ r' w, Pl (X r') w = A' ((ep, mergeAt p w.1.2 r'), w.2)) :
    acceptProb X (fun cv z => hybGen H Wa k (Pl cv) D z) = hybAcc H Wa k A' D ep := by
  unfold acceptProb hybAcc
  rw [← uprob_mergeAt k p ep
    (fun z : (Fin N → AttemptCoins m (Fin n → Fin ℓ → Bool) τ) × ρ' =>
      hybGen H Wa k A' D z = true)]
  congr 1
  funext y
  show (hybGen H Wa k (Pl (X y.1)) D (y.2.1, y.2.2) = true) = _
  rw [hybGen_update H Wa k D (hPl y.1 (y.2.1 k)) y.2.2]

/-- **The hybrid argument over the attempts with a planted worst `(e₀, π₀)`** (the concrete
content of Claim-129.d): if the planted attempt on a challenge from `X ep` is a `Wa` attempt
and on a challenge from `Y ep` an `H` attempt (each with the planted `ep` and merged
randomness), then for every `D` some hybrid index `k` and some `ep` satisfy
`distAdv (H_0) (H_N) D / N ≤ distAdv (X ep) (Y ep) (reduction at k planting ep)`.

**Proof sketch.** `exists_hybrid_gap` on `k ↦ acceptProb (hybStd H Wa N k) D` gives `k` with
gap `≥ distAdv / N`; the gap at `k` is `|E_{ep} (hybAcc Wa ep - hybAcc H ep)|`
(`hybGen_W`, `hybGen_H`, `uprob_hybGen_eq_uexp`), bounded by its value at some `ep`
(`CommitmentLemmas.exists_abs_uexp_le`), which is the reduction's advantage
(`acceptProb_hybGen_planted` twice). -/
theorem exists_hybRed_ge (hm : 0 < m) {N : ℕ} (hN : 0 < N)
    (H Wa : AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α) (D : Option α → ρ' → Bool)
    (p : Fin m → Fin n × Fin n)
    (Pl : Fin m × Equiv.Perm (Fin 3) → List Bool →
      AttemptCoins m (Fin n → Fin ℓ → Bool) τ → Option α)
    (X Y : Fin m × Equiv.Perm (Fin 3) → (Fin n → Fin ℓ → Bool) → List Bool)
    (hX : ∀ ep r' w, Pl ep (X ep r') w = Wa ((ep, mergeAt (p ep.1) w.1.2 r'), w.2))
    (hY : ∀ ep r' w, Pl ep (Y ep r') w = H ((ep, mergeAt (p ep.1) w.1.2 r'), w.2)) :
    ∃ (k : Fin N) (ep : Fin m × Equiv.Perm (Fin 3)),
      distAdv (hybStd H Wa N 0) (hybStd H Wa N N) D / N ≤
        distAdv (X ep) (Y ep) (fun cv z => hybGen H Wa k (Pl ep cv) D z) := by
  haveI : Nonempty (Fin m × Equiv.Perm (Fin 3)) := ⟨(⟨0, hm⟩, 1)⟩
  obtain ⟨k, hk, hgap⟩ := exists_hybrid_gap (fun i => acceptProb (hybStd H Wa N i) D) hN
  set kf : Fin N := ⟨k, hk⟩ with hkf
  have hPk : acceptProb (hybStd H Wa N k) D = uexp (hybAcc H Wa kf Wa D) := by
    rw [← uprob_hybGen_eq_uexp hm H Wa kf]
    unfold acceptProb
    congr 1
    funext z
    rw [← hybGen_W H Wa kf D z.1 z.2]
  have hPk1 : acceptProb (hybStd H Wa N (k + 1)) D = uexp (hybAcc H Wa kf H D) := by
    rw [← uprob_hybGen_eq_uexp hm H Wa kf]
    unfold acceptProb
    congr 1
    funext z
    rw [← hybGen_H H Wa kf D z.1 z.2]
  obtain ⟨ep₀, hep₀⟩ := CommitmentLemmas.exists_abs_uexp_le
    (fun ep => hybAcc H Wa kf Wa D ep - hybAcc H Wa kf H D ep)
  refine ⟨kf, ep₀, ?_⟩
  calc distAdv (hybStd H Wa N 0) (hybStd H Wa N N) D / N
      ≤ |acceptProb (hybStd H Wa N k) D - acceptProb (hybStd H Wa N (k + 1)) D| := hgap
    _ = |uexp (fun ep => hybAcc H Wa kf Wa D ep - hybAcc H Wa kf H D ep)| := by
        rw [hPk, hPk1, HardcoreBit.uexp_sub]
    _ ≤ |hybAcc H Wa kf Wa D ep₀ - hybAcc H Wa kf H D ep₀| := hep₀
    _ = _ := by
        rw [distAdv, acceptProb_hybGen_planted H Wa kf D (p ep₀.1) ep₀ (hX ep₀),
          acceptProb_hybGen_planted H Wa kf D (p ep₀.1) ep₀ (hY ep₀)]

end HybridCoins

end TCSlib.Cryptography.ColSimLemmas
