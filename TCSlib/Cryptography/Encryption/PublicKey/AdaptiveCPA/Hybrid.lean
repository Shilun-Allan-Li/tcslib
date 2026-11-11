/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity.ChallengeSim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hybrid challenge oracles under CPA

The single-to-many hybrid argument of [PS10, p. 103], extended to adaptive challenges, compares
experiments in which the `j`-th fresh challenge `⟨m₀, m₁⟩` is answered by an encryption of
`m_{sel j}` for a selector `sel : ℕ → Bool`. This file studies those oracles generically, on
bit-string oracles of arbitrary lengths (`bitSpec ins outs`), with the encryption an arbitrary
function `E` of the selected side, the query and the coins. Under CPA the decryption oracle
answers all-`false`.

* `hybImpl κ E sel` samples fresh coins for each of the first `κ` fresh challenges and records
  the ciphertexts in a history; once the cap `κ` is reached it repeats the latest ciphertext
  (all-`false` for an empty history).
* `tapeImpl κ E sel T kst` answers the `j`-th fresh challenge with the coins `T j` given in
  advance, except the `kst`-th, for which it samples coins. Drawing `T` uniformly gives the
  distribution of `hybImpl` (`expect_tapeImpl`); the proof resamples one coordinate at a time
  (`expect_sample_update`), using that the run from a history of length `j + 1` ignores the
  coins `T j` (`simulate_tapeImpl_congr`).

Two generic tools complete the file: `castImpl` transports an implementation along equal
length functions (`simulate_castImpl_toCompOn`), and `simulate_eq_of_abs` relates two
implementations through an abstraction of their states.

## Main definitions

* `AdaptiveCPA.castImpl`: an implementation read along equal length functions.
* `AdaptiveCPA.hybImpl`, `AdaptiveCPA.tapeImpl`: the hybrid challenge oracles.
* `AdaptiveCPA.extTape`: a finite family of coins, extended to every index.

## Main results

* `AdaptiveCPA.simulate_castImpl_toCompOn`: transport of a machine's run between two codecs.
* `AdaptiveCPA.simulate_eq_of_abs`: simulation through a state abstraction.
* `AdaptiveCPA.hybImpl_congr`: only the selector's values below the cap matter.
* `AdaptiveCPA.expect_sample_update`: resampling one coordinate of a uniform tuple.
* `AdaptiveCPA.expect_tapeImpl`: coins given in advance have the lazy distribution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  the single-to-many hybrid argument (book p. 103) and Definition 171.5.
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp ChallengeSim

/-! ### Transport along equal lengths -/

section Transport

variable {k : ℕ} {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

/-! ### Simulation through a state abstraction -/

/-- **Simulation through an abstraction of the state:** if every call of `impl₁` from the
abstract state `f s` is the call of `impl₂` from `s` with its new state abstracted, the same holds
for whole simulations: `simulate impl₁ c (f s) =
(simulate impl₂ c s).bind fun p => pure (p.1, f p.2)`.

**Proof sketch.** Induction on `c`; at a query, rewrite the call by the hypothesis and use the
induction hypothesis on each continuation after associativity. -/
theorem simulate_eq_of_abs {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {σ₁ σ₂ α : Type} (impl₁ : QueryImpl spec σ₁ spec') (impl₂ : QueryImpl spec σ₂ spec')
    (f : σ₂ → σ₁) (h : ∀ i x s, impl₁ i x (f s) = (impl₂ i x s).bind fun p => .pure (p.1, f p.2))
    (c : OracleComp spec α) (s : σ₂) :
    simulate impl₁ c (f s) = (simulate impl₂ c s).bind fun p => .pure (p.1, f p.2) := by
  induction c generalizing s with
  | pure a => simp only [simulate_pure, OracleComp.pure_bind]
  | query i x k ih =>
    rw [simulate_query, simulate_query, h, OracleComp.bind_assoc, OracleComp.bind_assoc]
    congr 1
    funext p
    rw [OracleComp.pure_bind]
    exact ih p.1 p.2

/-! ### The hybrid oracles -/

section Hybrid

variable {ins outs : Fin 2 → ℕ} {L : ℕ} {C : Type} [Fintype C] [Nonempty C]

/-- **The `sel`-hybrid of the adaptive CPA oracles** with cap `κ` and encryption `E`, on the
history `h` of issued ciphertexts:
- oracle `0` (decryption) answers all-`false`;
- oracle `1` (challenge) on `mm`, below the cap (`|h| < κ`), samples coins `r`, answers the
  ciphertext `c = E (sel |h|) mm r` (read at width `outs 1`) and records it, `h ↦ c :: h`;
- at the cap it repeats the latest ciphertext `h.headD 0`, all-`false` for `h = []`. -/
noncomputable def hybImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool))
    (sel : ℕ → Bool) : QueryImpl (bitSpec ins outs) (List (Fin L → Bool)) unifSpec
  | 0, _, h => .pure (zeroBits _, h)
  | 1, mm, h =>
    if h.length < κ then
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)), E (sel h.length) mm r :: h)
    else .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h)

variable (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool)) (sel : ℕ → Bool)

/-- Decryption answers all-`false` and keeps the history. -/
theorem hybImpl_zero (x : Fin (ins 0) → Bool) (h : List (Fin L → Bool)) :
    hybImpl (outs := outs) κ E sel 0 x h = .pure (zeroBits _, h) :=
  rfl

/-- A challenge below the cap samples coins `r` and records `c = E (sel |h|) mm r`:
`hybImpl κ E sel 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`. -/
theorem hybImpl_fresh (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ) :
    hybImpl (outs := outs) κ E sel 1 mm h =
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)),
          E (sel h.length) mm r :: h) := by
  rw [hybImpl, if_pos hh]

/-- At the cap a challenge repeats the latest ciphertext:
`hybImpl κ E sel 1 mm h = pure (padFin (outs 1) ⟦h.headD 0⟧, h)` when `κ ≤ |h|`. -/
theorem hybImpl_full (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : κ ≤ h.length) :
    hybImpl (outs := outs) κ E sel 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h) := by
  rw [hybImpl, if_neg (Nat.not_lt_of_ge hh)]

/-- **Only the selector below the cap matters:** if `sel j = sel' j` for every `j < κ`, the two
hybrids are the same implementation.

**Proof sketch.** The selector is read only at `|h|` in a fresh challenge, where `|h| < κ`. -/
theorem hybImpl_congr {sel' : ℕ → Bool} (hsel : ∀ j < κ, sel j = sel' j) :
    hybImpl (outs := outs) κ E sel = hybImpl κ E sel' := by
  funext i x h
  match i, x with
  | 0, x => rw [hybImpl_zero, hybImpl_zero]
  | 1, x =>
    by_cases hh : h.length < κ
    · rw [hybImpl_fresh κ E sel x h hh, hybImpl_fresh κ E sel' x h hh, hsel _ hh]
    · rw [hybImpl_full κ E sel x h (Nat.le_of_not_lt hh),
        hybImpl_full κ E sel' x h (Nat.le_of_not_lt hh)]

/-- **The hybrid with coins given in advance:** as `hybImpl κ E sel`, except that the `j`-th fresh
challenge uses the coins `T j`, unless `j = kst`, where it samples coins. -/
noncomputable def tapeImpl (T : ℕ → C) (kst : ℕ) :
    QueryImpl (bitSpec ins outs) (List (Fin L → Bool)) unifSpec
  | 0, _, h => .pure (zeroBits _, h)
  | 1, mm, h =>
    if h.length < κ then
      if h.length = kst then
        (ProbComp.sample C).bind fun r =>
          .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)), E (sel h.length) mm r :: h)
      else
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm (T h.length))),
          E (sel h.length) mm (T h.length) :: h)
    else .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h)

variable (T : ℕ → C) (kst : ℕ)

/-- With coins in advance, decryption answers all-`false` and keeps the history. -/
theorem tapeImpl_zero (x : Fin (ins 0) → Bool) (h : List (Fin L → Bool)) :
    tapeImpl (outs := outs) κ E sel T kst 0 x h = .pure (zeroBits _, h) :=
  rfl

/-- The `kst`-th fresh challenge samples its coins:
`tapeImpl κ E sel T kst 1 mm h = (sample C).bind fun r => pure (padFin (outs 1) ⟦c⟧, c :: h)`
with `c = E (sel |h|) mm r`, when `|h| < κ` and `|h| = kst`. -/
theorem tapeImpl_lazy (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ)
    (hk : h.length = kst) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      (ProbComp.sample C).bind fun r =>
        .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm r)),
          E (sel h.length) mm r :: h) := by
  rw [tapeImpl, if_pos hh, if_pos hk]

/-- Another fresh challenge uses its coins in advance:
`tapeImpl κ E sel T kst 1 mm h = pure (padFin (outs 1) ⟦c⟧, c :: h)` with
`c = E (sel |h|) mm (T |h|)`, when `|h| < κ` and `|h| ≠ kst`. -/
theorem tapeImpl_eager (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : h.length < κ)
    (hk : h.length ≠ kst) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (E (sel h.length) mm (T h.length))),
        E (sel h.length) mm (T h.length) :: h) := by
  rw [tapeImpl, if_pos hh, if_neg hk]

/-- At the cap a challenge repeats the latest ciphertext, as in `hybImpl_full`. -/
theorem tapeImpl_full (mm : Fin (ins 1) → Bool) (h : List (Fin L → Bool)) (hh : κ ≤ h.length) :
    tapeImpl (outs := outs) κ E sel T kst 1 mm h =
      .pure (padFin (outs 1) (List.ofFn (h.headD (zeroBits L))), h) := by
  rw [tapeImpl, if_neg (Nat.not_lt_of_ge hh)]

/-- **The run ignores the coins of challenges already issued:** if `T` and `T'` agree at every
index `m ≥ |h|`, the runs from the history `h` agree.

**Proof sketch.** Induction on the computation. A fresh challenge from a history `h'` with
`|h| ≤ |h'|` reads only `T |h'|`, and moves to a longer history. -/
theorem simulate_tapeImpl_congr {α : Type} (T' : ℕ → C) (c : OracleComp (bitSpec ins outs) α)
    (h : List (Fin L → Bool)) (hT : ∀ m, h.length ≤ m → T m = T' m) :
    simulate (tapeImpl κ E sel T kst) c h = simulate (tapeImpl κ E sel T' kst) c h := by
  induction c generalizing h with
  | pure a => rw [simulate_pure, simulate_pure]
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      rw [simulate_query, simulate_query, tapeImpl_zero, tapeImpl_zero, OracleComp.pure_bind,
        OracleComp.pure_bind]
      exact ih _ h hT
    | 1, x, k, ih =>
      have hT' : ∀ m, (h.length + 1) ≤ m → T m = T' m := fun m hm => hT m (by omega)
      by_cases hh : h.length < κ
      · by_cases hk : h.length = kst
        · rw [simulate_query, simulate_query, tapeImpl_lazy κ E sel T kst x h hh hk,
            tapeImpl_lazy κ E sel T' kst x h hh hk, OracleComp.bind_assoc,
            OracleComp.bind_assoc]
          congr 1
          funext r
          rw [OracleComp.pure_bind, OracleComp.pure_bind]
          exact ih _ _ hT'
        · rw [simulate_query, simulate_query, tapeImpl_eager κ E sel T kst x h hh hk,
            tapeImpl_eager κ E sel T' kst x h hh hk, OracleComp.pure_bind,
            OracleComp.pure_bind, hT h.length le_rfl]
          exact ih _ _ hT'
      · rw [simulate_query, simulate_query, tapeImpl_full κ E sel T kst x h (Nat.le_of_not_lt hh),
          tapeImpl_full κ E sel T' kst x h (Nat.le_of_not_lt hh), OracleComp.pure_bind,
          OracleComp.pure_bind]
        exact ih _ h hT

end Hybrid

/-! ### Coins in advance have the lazy distribution -/

section Eager

variable {C : Type} [Nonempty C]

/-- A family of `κ` coin strings, extended to every index by an arbitrary value:
`extTape T m = T m` for `m < κ`. -/
noncomputable def extTape {κ : ℕ} (T : Fin κ → C) (m : ℕ) : C :=
  if hm : m < κ then T ⟨m, hm⟩ else Classical.arbitrary C

/-- Below `κ` the extended family is the family: `extTape T m = T ⟨m, hm⟩`. -/
theorem extTape_of_lt {κ : ℕ} (T : Fin κ → C) {m : ℕ} (hm : m < κ) :
    extTape T m = T ⟨m, hm⟩ := by
  rw [extTape, dif_pos hm]

/-- Changing one coordinate `j` of `T` changes its extension only at `j`. -/
theorem extTape_update {κ : ℕ} (T : Fin κ → C) (j : Fin κ) (r : C) {m : ℕ} (hm : m ≠ j) :
    extTape (Function.update T j r) m = extTape T m := by
  by_cases h : m < κ
  · rw [extTape_of_lt _ h, extTape_of_lt _ h, Function.update_of_ne]
    exact fun h' => hm (congrArg Fin.val h')
  · rw [extTape, extTape, dif_neg h, dif_neg h]

variable [Fintype C]

/-- **Resampling one coordinate of a uniform tuple:** if `F r T` ignores the coordinate `j` of
`T`, then `𝔼_T F (T j) T = 𝔼_r 𝔼_T F r T`.

**Proof sketch.** The map `(T, r) ↦ (T[j ↦ r], T j)` is an involution of `(Fin κ → C) × C`, so
it preserves the uniform average (`expect_sample_equiv`). It carries `F (T j) T` to
`F r (T[j ↦ r]) = F r T`. Split the products (`expect_sample_prod`), drop the unused sample
(`expect_const`) and exchange the order (`expect_sample_comm`). -/
theorem expect_sample_update {κ : ℕ} (j : Fin κ) (F : C → (Fin κ → C) → ℝ)
    (hF : ∀ r r' T, F r (Function.update T j r') = F r T) :
    expect (sample (Fin κ → C)) (fun T => F (T j) T) =
      expect (sample C) fun r => expect (sample (Fin κ → C)) fun T => F r T := by
  let e : (Fin κ → C) × C ≃ (Fin κ → C) × C :=
    { toFun := fun p => (Function.update p.1 j p.2, p.1 j)
      invFun := fun p => (Function.update p.1 j p.2, p.1 j)
      left_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self]
      right_inv := fun p => by
        simp only [Function.update_self, Function.update_idem, Function.update_eq_self] }
  have he := expect_sample_equiv e (fun p => F (p.1 j) p.1)
  have hl : (fun p : (Fin κ → C) × C => F ((e p).1 j) (e p).1) = fun p => F p.2 p.1 := by
    funext p
    show F ((Function.update p.1 j p.2) j) (Function.update p.1 j p.2) = F p.2 p.1
    rw [Function.update_self, hF]
  rw [hl, expect_sample_prod, expect_sample_prod] at he
  rw [← expect_sample_comm, he]
  refine congrArg _ (funext fun T => ?_)
  exact (expect_const _ _).symm

variable {ins outs : Fin 2 → ℕ} {L : ℕ}

/-- **Coins in advance have the lazy distribution:** for every `kst` and every function `G` of
the output and the final history, averaging over uniform coins `T` in advance gives the lazy
hybrid: `𝔼_T 𝔼[G (simulate (tapeImpl κ E sel (extTape T) kst) c h)] =
𝔼[G (simulate (hybImpl κ E sel) c h)]`.

**Proof sketch.** Induction on `c`, generalizing the history. Decryption queries and challenges
at the cap are answered alike. The `kst`-th fresh challenge samples coins on both sides; exchange
the order of the two samples (`expect_sample_comm`) and apply the induction hypothesis. Another
fresh challenge, the `j`-th, reads `T j` on the left; the continuation runs from a history of
length `j + 1`, so it ignores `T j` (`simulate_tapeImpl_congr`, `extTape_update`), and
`expect_sample_update` replaces `T j` by fresh coins; then apply the induction hypothesis. -/
theorem expect_tapeImpl (κ : ℕ) (E : Bool → (Fin (ins 1) → Bool) → C → (Fin L → Bool))
    (sel : ℕ → Bool) (kst : ℕ) {α : Type} (G : α × List (Fin L → Bool) → ℝ)
    (c : OracleComp (bitSpec ins outs) α) (h : List (Fin L → Bool)) :
    expect (sample (Fin κ → C))
        (fun T => expect (simulate (tapeImpl κ E sel (extTape T) kst) c h) G) =
      expect (simulate (hybImpl κ E sel) c h) G := by
  induction c generalizing h with
  | pure a =>
    simp only [simulate_pure, expect_pure]
    exact expect_const _ _
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih =>
      simp only [simulate_query, tapeImpl_zero, hybImpl_zero, OracleComp.pure_bind]
      exact ih _ h
    | 1, x, k, ih =>
      by_cases hh : h.length < κ
      · rw [simulate_query, hybImpl_fresh κ E sel x h hh, OracleComp.bind_assoc, expect_bind]
        simp only [OracleComp.pure_bind]
        by_cases hk : h.length = kst
        · simp only [simulate_query, tapeImpl_lazy κ E sel _ kst x h hh hk, OracleComp.bind_assoc,
            expect_bind, OracleComp.pure_bind]
          rw [expect_sample_comm]
          exact congrArg _ (funext fun r => ih _ _)
        · simp only [simulate_query, tapeImpl_eager κ E sel _ kst x h hh hk, OracleComp.pure_bind]
          let j : Fin κ := ⟨h.length, hh⟩
          have hj : ∀ T : Fin κ → C, extTape T h.length = T j := fun T => extTape_of_lt T hh
          simp only [hj]
          refine (expect_sample_update j (fun r T => expect (simulate
            (tapeImpl κ E sel (extTape T) kst) (k (padFin (outs 1) (List.ofFn
              (E (sel h.length) x r)))) (E (sel h.length) x r :: h)) G) ?_).trans ?_
          · intro r r' T
            refine congrArg (fun c => expect c G)
              (simulate_tapeImpl_congr κ E sel _ kst _ _ _ fun m hm => ?_)
            rw [List.length_cons] at hm
            exact extTape_update T j r' (by
              intro hmj
              have : m = h.length := hmj
              omega)
          · exact congrArg _ (funext fun r => ih _ _)
      · simp only [simulate_query, tapeImpl_full κ E sel _ kst x h (Nat.le_of_not_lt hh),
          hybImpl_full κ E sel x h (Nat.le_of_not_lt hh), OracleComp.pure_bind]
        exact ih _ h

end Eager

end TCSlib.Cryptography.Composability.AdaptiveCPA
