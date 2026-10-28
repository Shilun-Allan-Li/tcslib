/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Simulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Statistical closeness of the graph isomorphism simulator

The probability bookkeeping behind Theorem 122.3 of `ZeroKnowledge/GraphIsomorphismZK.lean`
(`gi_statZK`): the string-level view of a cheating verifier `V'` in one iteration of
[PS10, Protocol 120.6] and the output of the string simulator `GIZK.sim` are statistically
close, assuming the typed closeness of the truncated simulator (Thm-122.3.trunc, proved in the
main file and passed here as a hypothesis).

The typed objects of the main file (`giRealView`, `giSimAttempt`, `giSimTrunc`) are shadowed
by `GIZK.realView`, `GIZK.simAttempt`, `GIZK.simTrunc` with identical bodies. The chain of
closeness steps is

1. the real view with the rejection-sampled `π` is within `permFailBound n` of the real view
   with a uniform `π` (`statClose_samplePerm_long`, `StatClose.prod`, `StatClose.map`);
2. the typed truncated simulator is within `2^{-n}` of the real view (hypothesis);
3. the string simulator reads its tape as `n` independent blocks `(π'_t, b'_t, r_t)`
   (`readBlocks`, a composition of maps pushing uniform to uniform), and replacing the `n`
   rejection-sampled `π'_t` by uniform ones costs `n · permFailBound n` (`statClose_pi`).

The real view is computed from `exec` (`viewV_encode`) and the string simulator is identified
with the typed one on an encoded instance (`attemptStr_ofFn`, `sim_ofFn_eq`).

## Main definitions

* `TCSlib.Cryptography.GIZK.realView`, `GIZK.simAttempt`, `GIZK.simTrunc` — shadows of the
  typed layer.
* `TCSlib.Cryptography.GIZK.vstar`, `GIZK.encView` — the cheating verifier as a function of
  the graph and its coins, and the string encoding of a typed view.
* `TCSlib.Cryptography.GIZK.tapeBlock`, `GIZK.blockFields`, `GIZK.readBlocks` — reading a
  tape as blocks and a block as its three fields.

## Main results

* `TCSlib.Cryptography.GIZK.statClose_pi` — closeness is preserved by `N`-fold independent
  products, with bound `N · δ`.
* `TCSlib.Cryptography.GIZK.pushesUniform_readBlocks` — the block reading of a uniform tape
  is uniform.
* `TCSlib.Cryptography.GIZK.viewV_encode` — the encoded view of `V'` in the real execution.
* `TCSlib.Cryptography.GIZK.sim_ofFn_eq` — the string simulator on an encoded instance is the
  encoded typed simulator on the sampled blocks.
* `TCSlib.Cryptography.GIZK.statClose_real_sim` — the assembled closeness bound
  `2^{-n} + (n + 1) · permFailBound n`.
* `TCSlib.Cryptography.GIZK.negligible_delta` — the bound is negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge proofs, Theorem 122.3 and Algorithm 123.4, pp. 122–124.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GIZK

open Complexity Turing Finset

/-! ### Shadows of the typed layer -/

/-- Shadow of `giRealView`: the view `(r, π(G₀), γ)` of a cheating verifier `V*` in one real
iteration on the prover's coins `π` and `V*`'s coins `r`. -/
def realView {n : ℕ} {ρ : Type*} (G₀ : Graph n) (σ : Equiv.Perm (Fin n)) (V : Graph n → ρ → Bool)
    (w : Equiv.Perm (Fin n) × ρ) : ρ × Graph n × Equiv.Perm (Fin n) :=
  (w.2, permGraph G₀ w.1, if V (permGraph G₀ w.1) w.2 then w.1 * σ⁻¹ else w.1)

/-- Shadow of `giSimAttempt`: one attempt of [PS10, Algorithm 123.4] on the coins
`((π', b'), r)`. -/
def simAttempt {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool)
    (c : (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  if V (permGraph (cond c.1.2 G₁ G₀) c.1.1) c.2 = c.1.2 then
    some (c.2, permGraph (cond c.1.2 G₁ G₀) c.1.1, c.1.1)
  else none

/-- Shadow of `giSimTrunc`: the first successful of `N` attempts, `none` if all fail. -/
def simTrunc {n : ℕ} {ρ : Type*} (G₀ G₁ : Graph n) (V : Graph n → ρ → Bool) (N : ℕ)
    (c : Fin N → (Equiv.Perm (Fin n) × Bool) × ρ) : Option (ρ × Graph n × Equiv.Perm (Fin n)) :=
  (List.finRange N).findSome? fun t => simAttempt G₀ G₁ V (c t)

/-- The cheating verifier `V'` on common input `x` and auxiliary input `z` as a function of
the received graph and of its typed coins: the first bit of its reply to `[encGraph H]`. -/
def vstar (V' : Strategy) (x z : List Bool) {n : ℕ} (H : Graph n) (r : V'.Coins x.length) : Bool :=
  (V'.next x z (List.ofFn r) [encGraph H]).headD false

/-- The string encoding of a typed view `(r, H, γ)` of `V'`: `⟨⟨x, z⟩, ⟨r, [encGraph H, encPerm γ]⟩⟩`. -/
def encView (V' : Strategy) (x z : List Bool) {n : ℕ}
    (v : V'.Coins x.length × Graph n × Equiv.Perm (Fin n)) : List Bool :=
  View.encode ⟨x, z, List.ofFn v.1, [encGraph v.2.1, encPerm v.2.2]⟩

/-! ### Tapes and the permutation sampler -/

/-- Restricting a uniform tuple of `c` entries to its first `m ≤ c` entries gives a uniform
tuple: the tuple is the pair (prefix, suffix) through `finSumFinEquiv`, and the first
projection pushes uniform to uniform. -/
theorem pushesUniform_castLE {B : Type*} [Fintype B] [Nonempty B] {m c : ℕ} (h : m ≤ c) :
    HardcoreBit.PushesUniform (fun t : Fin c → B => fun i : Fin m => t (Fin.castLE h i)) := by
  let e : (Fin c → B) ≃ (Fin m → B) × (Fin (c - m) → B) :=
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl B)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl B)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he : ∀ t : Fin c → B, (e t).1 = fun i : Fin m => t (Fin.castLE h i) := by
    intro t
    funext i
    simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, finCongr_symm, finCongr_apply,
      finSumFinEquiv_apply_left]
    congr 1
  have := (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst
  simpa only [he] using this

/-- An entry of the list of a tape below its length. -/
theorem getD_ofFn_lt {c : ℕ} (t : Fin c → Bool) {i : ℕ} (hi : i < c) (d : Bool) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The index `(i T + t) k + j` of a coin-table entry is below `n T k`. -/
theorem coinTable_index_lt {n T k : ℕ} (i : Fin n) (t : Fin T) (j : Fin k) :
    ((i : ℕ) * T + t) * k + j < n * T * k := by
  have h1 : (i : ℕ) * T + t + 1 ≤ n * T := by
    have hi : (i : ℕ) + 1 ≤ n := i.isLt
    have ht : (t : ℕ) + 1 ≤ T := t.isLt
    calc (i : ℕ) * T + t + 1 ≤ i * T + T := by omega
      _ = (i + 1) * T := by ring
      _ ≤ n * T := Nat.mul_le_mul_right T hi
  calc ((i : ℕ) * T + t) * k + j < ((i : ℕ) * T + t) * k + k := by omega
    _ = ((i : ℕ) * T + t + 1) * k := by ring
    _ ≤ n * T * k := Nat.mul_le_mul_right k h1

/-- The coin table of a tape only depends on the first `n T k` bits. -/
theorem coinTable_ofFn_castLE {n T k c : ℕ} (h : n * T * k ≤ c) (t : Fin c → Bool) :
    coinTable n T k (List.ofFn t) =
      coinTable n T k (List.ofFn fun i : Fin (n * T * k) => t (Fin.castLE h i)) := by
  funext i t' j
  simp only [coinTable_apply]
  rw [getD_ofFn_lt t (lt_of_lt_of_le (coinTable_index_lt i t' j) h),
    getD_ofFn_lt _ (coinTable_index_lt i t' j)]
  rfl

/-- The permutation sampler reads only the first `permCoinLen n` bits of its tape. -/
theorem samplePerm_ofFn_castLE {n c : ℕ} (h : permCoinLen n ≤ c) (t : Fin c → Bool) :
    samplePerm n (List.ofFn t) =
      samplePerm n (List.ofFn fun i : Fin (permCoinLen n) => t (Fin.castLE h i)) := by
  unfold samplePerm
  rw [coinTable_ofFn_castLE h t]
  rfl

/-- On any tape of at least `permCoinLen n` bits the sampler is within `permFailBound n` of a
uniform permutation (`statClose_samplePerm`, `samplePerm_ofFn_castLE`, `pushesUniform_castLE`). -/
theorem statClose_samplePerm_long {n c : ℕ} (h : permCoinLen n ≤ c) :
    StatClose (fun t : Fin c → Bool => samplePerm n (List.ofFn t))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) := by
  have := (statClose_samplePerm n).comp_pushesUniform (pushesUniform_castLE h)
  intro T
  have hT := this T
  simpa only [samplePerm_ofFn_castLE h] using hT

/-! ### Products of close samplers -/

/-- Closeness is preserved by `N`-fold independent products, with bound `N · δ`.

**Proof sketch.** Induction on `N`. For `N = 0` both samplers are the constant `Fin.elim0`
and the two probabilities agree. For `N + 1`, split the tuples as (head, tail) by
`Fin.consEquiv` (`StatClose.comp_equiv_left`/`right`): the pair sampler is `StatClose.prod` of
`h` and the induction hypothesis, mapped by `Fin.cons` (`StatClose.map`), with bound
`δ + N δ`. -/
theorem statClose_pi {σ τ γ : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (N : ℕ) :
    StatClose (fun s : Fin N → σ => fun t => X (s t)) (fun u : Fin N → τ => fun t => Y (u t))
      (N * δ) := by
  induction N with
  | zero =>
    intro T
    haveI : Nonempty (Fin 0 → σ) := ⟨Fin.elim0⟩
    haveI : Nonempty (Fin 0 → τ) := ⟨Fin.elim0⟩
    have hX : ∀ s : Fin 0 → σ, (fun t => X (s t)) = (fun t : Fin 0 => (Fin.elim0 t : γ)) :=
      fun s => funext fun t => t.elim0
    have hY : ∀ u : Fin 0 → τ, (fun t => Y (u t)) = (fun t : Fin 0 => (Fin.elim0 t : γ)) :=
      fun u => funext fun t => t.elim0
    have h1 : uprob (fun s : Fin 0 → σ => T (fun t => X (s t))) =
        uprob (fun _ : Fin 0 → σ => T (fun t : Fin 0 => (Fin.elim0 t : γ))) :=
      OneWay.uprob_congr fun s => by rw [hX s]
    have h2 : uprob (fun u : Fin 0 → τ => T (fun t => Y (u t))) =
        uprob (fun _ : Fin 0 → τ => T (fun t : Fin 0 => (Fin.elim0 t : γ))) :=
      OneWay.uprob_congr fun u => by rw [hY u]
    show |uprob (fun s : Fin 0 → σ => T (fun t => X (s t))) -
      uprob (fun u : Fin 0 → τ => T (fun t => Y (u t)))| ≤ ((0 : ℕ) : ℝ) * δ
    rw [h1, h2, Nat.cast_zero, zero_mul]
    by_cases hT : T (fun t : Fin 0 => (Fin.elim0 t : γ))
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | succ N ih =>
    have hp := (h.prod ih).map (fun p : γ × (Fin N → γ) => (Fin.cons (α := fun _ => γ) p.1 p.2))
    have hl : StatClose
        (fun s : Fin (N + 1) → σ => Fin.cons (α := fun _ => γ) (X (s 0)) (fun t => X (s t.succ)))
        (fun u : Fin (N + 1) → τ => Fin.cons (α := fun _ => γ) (Y (u 0)) (fun t => Y (u t.succ)))
        (δ + N * δ) :=
      (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
        (Fin.consEquiv fun _ => τ).symm
    have e1 : (fun s : Fin (N + 1) → σ => fun t => X (s t)) =
        fun s => Fin.cons (α := fun _ => γ) (X (s 0)) (fun t => X (s t.succ)) := by
      funext s t
      refine Fin.cases ?_ (fun j => ?_) t
      · simp
      · simp
    have e2 : (fun u : Fin (N + 1) → τ => fun t => Y (u t)) =
        fun u => Fin.cons (α := fun _ => γ) (Y (u 0)) (fun t => Y (u t.succ)) := by
      funext u t
      refine Fin.cases ?_ (fun j => ?_) t
      · simp
      · simp
    rw [e1, e2]
    refine hl.mono (le_of_eq ?_)
    push_cast
    ring

/-! ### Blocks of a tape -/

/-- Block `t` of a tape of `M · L` bits: the positions `t L, …, t L + L - 1`. -/
def tapeBlock (M L : ℕ) (r : Fin (M * L) → Bool) (t : Fin M) (i : Fin L) : Bool :=
  r ⟨t * L + i, by
    calc (t : ℕ) * L + i < (t : ℕ) * L + L := by omega
      _ = ((t : ℕ) + 1) * L := by ring
      _ ≤ M * L := Nat.mul_le_mul_right L t.isLt⟩

/-- Reading a tape as `M` blocks of `L` bits is a bijection (injective, and the two types
have `2^{M L}` elements). -/
theorem tapeBlock_bijective (M L : ℕ) : Function.Bijective (tapeBlock M L) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun r r' h => ?_, ?_⟩
  · funext k
    rcases Nat.eq_zero_or_pos L with hL | hL
    · exact absurd k.isLt (by simp [hL])
    · have ht : (k : ℕ) / L < M := (Nat.div_lt_iff_lt_mul hL).2 k.isLt
      have hi : (k : ℕ) % L < L := Nat.mod_lt _ hL
      have := congrFun (congrFun h ⟨k / L, ht⟩) ⟨k % L, hi⟩
      simp only [tapeBlock] at this
      have e : (⟨(k : ℕ) / L * L + k % L, by
          calc (k : ℕ) / L * L + k % L = k := Nat.div_add_mod' _ _
            _ < M * L := k.isLt⟩ : Fin (M * L)) = k := Fin.ext (Nat.div_add_mod' _ _)
      rwa [e] at this
  · simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, ← pow_mul]
    ring_nf

/-- The `t`-th coin slice of the list of a tape is the list of its `t`-th block. -/
theorem coinSlice_ofFn {M L : ℕ} (r : Fin (M * L) → Bool) (t : Fin M) :
    coinSlice L t (List.ofFn r) = List.ofFn (tapeBlock M L r t) := by
  have hle : (t : ℕ) * L + L ≤ M * L := by
    calc (t : ℕ) * L + L = ((t : ℕ) + 1) * L := by ring
      _ ≤ M * L := Nat.mul_le_mul_right L t.isLt
  apply List.ext_getElem
  · simp only [coinSlice, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [coinSlice, List.getElem_take, List.getElem_drop, List.getElem_ofFn, tapeBlock]

/-- The three fields of a coin block of `1 + P + Q` bits: the permutation coins (positions
`1, …, P`), the guessed bit (position `0`) and the verifier's tape (positions `1 + P, …`). -/
def blockFields (P Q : ℕ) (g : Fin (1 + P + Q) → Bool) : ((Fin P → Bool) × Bool) × (Fin Q → Bool) :=
  ((fun i => g ⟨1 + i, by omega⟩, g ⟨0, by omega⟩), fun j => g ⟨1 + P + j, by omega⟩)

/-- Splitting a block into its fields is a bijection. -/
theorem blockFields_bijective (P Q : ℕ) : Function.Bijective (blockFields P Q) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun g g' h => ?_, ?_⟩
  · simp only [blockFields, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h0⟩, h2⟩ := h
    funext k
    rcases k with ⟨k, hk⟩
    by_cases hk0 : k = 0
    · subst hk0
      exact h0
    · by_cases hkP : k < 1 + P
      · have := congrFun h1 ⟨k - 1, by omega⟩
        convert this using 2 <;> exact Fin.ext (by simp; omega)
      · have := congrFun h2 ⟨k - (1 + P), by omega⟩
        convert this using 2 <;> exact Fin.ext (by simp; omega)
  · simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    ring

/-- The first bit of the list of a block. -/
theorem headD_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    (List.ofFn g).headD false = g ⟨0, by omega⟩ := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_ofFn, dif_pos (by omega)]
  rfl

/-- The permutation coins of the list of a block. -/
theorem drop_one_take_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    ((List.ofFn g).drop 1).take P = List.ofFn (fun i : Fin P => g ⟨1 + i, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- The verifier's tape of the list of a block. -/
theorem drop_ofFn_block {P Q : ℕ} (g : Fin (1 + P + Q) → Bool) :
    (List.ofFn g).drop (1 + P) = List.ofFn (fun j : Fin Q => g ⟨1 + P + j, by omega⟩) := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    simp only [List.getElem_drop, List.getElem_ofFn]

/-- The first `n ≤ M` blocks of a tape of `M` blocks of `1 + P + Q` bits, each split into its
fields. -/
def readBlocks (P Q M n : ℕ) (hn : n ≤ M) (r : Fin (M * (1 + P + Q)) → Bool) (t : Fin n) :
    ((Fin P → Bool) × Bool) × (Fin Q → Bool) :=
  blockFields P Q (tapeBlock M (1 + P + Q) r (Fin.castLE hn t))

/-- Reading the first `n` blocks of a uniform tape gives `n` independent uniform blocks: a
bijection (`tapeBlock_bijective`), a restriction (`pushesUniform_castLE`) and a blockwise
bijection (`blockFields_bijective`). -/
theorem pushesUniform_readBlocks (P Q M n : ℕ) (hn : n ≤ M) :
    HardcoreBit.PushesUniform (readBlocks P Q M n hn) := by
  have h1 := HardcoreBit.pushesUniform_equiv (Equiv.ofBijective _ (tapeBlock_bijective M (1 + P + Q)))
  have h2 := pushesUniform_castLE (B := Fin (1 + P + Q) → Bool) hn
  have h3 := HardcoreBit.pushesUniform_equiv
    (Equiv.piCongrRight fun _ : Fin n => Equiv.ofBijective _ (blockFields_bijective P Q))
  exact (h1.comp h2).comp h3

/-! ### The string simulator on an encoded instance -/

/-- One attempt of the string simulator on an encoded instance and a full coin block is the
encoding of the typed attempt on the block's fields (with the rejection-sampled permutation).

**Proof sketch.** Unfold `attemptStr`; the block's fields are read by `headD_ofFn_block`,
`drop_one_take_ofFn_block`, `drop_ofFn_block`; the vertex count `instanceVertexCount x = n`
and the graphs `instanceG₀ x = G₀`, `instanceG₁ x = G₁` are transported along
`pairFstD_pairEncode`, `decGraph_encGraph` (dependent positions, rewritten at once) and
`decGraphAt_encGraph`; then both sides are `if V*(H, r) = b' then some … else none`. -/
theorem attemptStr_ofFn (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool)
    (g : Fin (1 + ((encInstance G₀ G₁).length + 1) ^ 2 + V'.coinLen (encInstance G₀ G₁).length) → Bool) :
    attemptStr V' (encInstance G₀ G₁) z (List.ofFn g) =
      Option.map (encView V' (encInstance G₀ G₁) z)
        (simAttempt G₀ G₁ (vstar V' (encInstance G₀ G₁) z)
          ((samplePerm n (List.ofFn (blockFields _ _ g).1.1), (blockFields _ _ g).1.2),
            (blockFields _ _ g).2)) := by
  simp only [attemptStr, instanceG₀, instanceG₁, instanceVertexCount, headD_ofFn_block,
    drop_one_take_ofFn_block, drop_ofFn_block]
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _,
    show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _]
  generalize hm : Nat.sqrt (encGraph G₀).length = m
  obtain rfl : m = n := by rw [← hm, length_encGraph, Nat.sqrt_eq]
  simp only [decGraphAt_encGraph, blockFields]
  cases hb : g ⟨0, by omega⟩ <;>
    simp only [simAttempt, vstar, cond_false, cond_true, Bool.false_eq_true, if_false, if_true] <;>
    split_ifs <;> rfl

/-- The string simulator on an encoded instance with a tape of `M ≥ n` blocks is the
encoded typed simulator on the first `n` blocks, read by `readBlocks` with the
rejection-sampled permutations (`instanceVertexCount_encInstance`, `List.map_coe_finRange`,
`List.findSome?_map`, `List.map_findSome?`, `coinSlice_ofFn`, `attemptStr_ofFn`). -/
theorem sim_ofFn_eq (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) {M : ℕ} (hn : n ≤ M)
    (r : Fin (M * blockLen V' (encInstance G₀ G₁).length) → Bool) :
    sim V' (encInstance G₀ G₁) z (List.ofFn r) =
      (Option.map (encView V' (encInstance G₀ G₁) z)
        (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n fun t =>
          ((samplePerm n (List.ofFn (readBlocks _ _ M n hn r t).1.1), (readBlocks _ _ M n hn r t).1.2),
            (readBlocks _ _ M n hn r t).2))).getD [] := by
  unfold sim
  rw [instanceVertexCount_encInstance, ← List.map_coe_finRange, List.findSome?_map, simTrunc,
    List.map_findSome?]
  congr 2
  funext t
  simp only [Function.comp_apply]
  rw [show ((t : Fin n) : ℕ) = ((Fin.castLE hn t : Fin M) : ℕ) from rfl, coinSlice_ofFn,
    attemptStr_ofFn]
  rfl

/-! ### The real view -/

/-- The first message of the graph isomorphism prover on an encoded instance: `π(G₀)`. -/
theorem giProver_next_nil {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) :
    giProver.next (encInstance G₀ G₁) y r [] = encGraph (permGraph G₀ (samplePerm n r)) := by
  show encGraph (permGraph (decGraph (pairFstD (encInstance G₀ G₁))).2
    (samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r)) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]

/-- The reply of the graph isomorphism prover with witness `encPerm σ` to the challenge `m`. -/
theorem giProver_next_cons {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r m : List Bool)
    (h : List (List Bool)) :
    giProver.next (encInstance G₀ G₁) (encPerm σ) r (m :: h) =
      encPerm (if m.headD false then samplePerm n r * σ⁻¹ else samplePerm n r) := by
  show encPerm (if ((m :: h).headD []).headD false then
      samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r *
        (decPerm (decGraph (pairFstD (encInstance G₀ G₁))).1 (encPerm σ))⁻¹
    else samplePerm (decGraph (pairFstD (encInstance G₀ G₁))).1 r) = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _, decGraph_encGraph]
  simp only [decPerm_encPerm, List.headD_cons]

/-- The messages received by the verifier in the three moves of a prover-first execution:
the prover's first message, and its reply to the verifier's answer to it (`exec` unfolded,
`moverIsV`). -/
theorem exec_three_snd (P V : Strategy) (x y z rP rV : List Bool) :
    (exec P V false x y z rP rV 3).2 =
      [P.next x y rP [], P.next x y rP [V.next x z rV [P.next x y rP []]]] := by
  simp [exec, moverIsV]

/-- The encoded view of a cheating verifier `V'` in one real iteration of
[PS10, Protocol 120.6] against the honest prover with witness `encPerm σ`: the encoding of
the typed real view on the rejection-sampled `π` (`exec_three_snd`, `giProver_next_nil`,
`giProver_next_cons`). -/
theorem viewV_encode (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z : List Bool)
    (r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁)) :
    ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode =
      encView V' (encInstance G₀ G₁) z
        (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) (samplePerm n (List.ofFn r.1), r.2)) := by
  show View.encode ⟨encInstance G₀ G₁, z, List.ofFn r.2,
    (exec giProver V' false (encInstance G₀ G₁) (encPerm σ) z (List.ofFn r.1) (List.ofFn r.2) 3).2⟩ = _
  rw [exec_three_snd, giProver_next_nil, giProver_next_cons]
  rfl

/-! ### Assembly -/

/-- An encoded instance on `n` vertices has length at least `2n²` (and at least `n`). -/
theorem two_mul_sq_le_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    2 * (n * n) ≤ (encInstance G₀ G₁).length := by
  rw [length_encInstance]
  omega

/-- The vertex count is at most the length of an encoded instance (`Nat.le_mul_self`). -/
theorem le_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : n ≤ (encInstance G₀ G₁).length := by
  rw [length_encInstance]
  have := Nat.le_mul_self n
  omega

/-- Step 1 of the assembly: the real view with the rejection-sampled `π` is within
`permFailBound n` of the real view with a uniform `π` (`viewV_encode`,
`statClose_samplePerm_long`, `StatClose.prod`, `StatClose.map`). -/
theorem statClose_real_ideal (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (z : List Bool) :
    StatClose
      (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) =>
        ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode)
      (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length =>
        encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
      (permFailBound n + 0) := by
  have hP : permCoinLen n ≤ (PolyExpr.normal 1 2).eval (encInstance G₀ G₁).length := by
    rw [PolyExpr.eval_normal, one_mul]
    exact permCoinLen_le (two_mul_sq_le_length_encInstance G₀ G₁)
  have h := ((statClose_samplePerm_long hP).prod
    (StatClose.refl (fun r : V'.Coins (encInstance G₀ G₁).length => r))).map
    (fun w => encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
  intro T
  have hT := h T
  simpa only [viewV_encode] using hT

/-- Step 3 of the assembly: the encoded typed simulator on uniform blocks is within
`n · permFailBound n` of the string simulator on a tape of `|x| · blockLen V' |x|` bits.

**Proof sketch.** The block sampler `(π', b', r) ↦ ((samplePerm π', b'), r)` is within
`permFailBound n` of the identity (`statClose_samplePerm_long`, `StatClose.prod`), so its
`n`-fold product is within `n · permFailBound n` (`statClose_pi`); the tape read as `n` blocks
is uniform (`pushesUniform_readBlocks`, `StatClose.comp_pushesUniform`); map both sides by the
encoded truncated simulator (`StatClose.map`) and identify the string simulator with it
(`sim_ofFn_eq`). -/
theorem statClose_typed_string (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (z : List Bool) :
    StatClose
      (fun c : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
        (Option.map (encView V' (encInstance G₀ G₁) z)
          (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n c)).getD [])
      (fun r : Fin ((encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) → Bool =>
        sim V' (encInstance G₀ G₁) z (List.ofFn r))
      (n * (permFailBound n + 0 + 0)) := by
  have hP' : permCoinLen n ≤ ((encInstance G₀ G₁).length + 1) ^ 2 :=
    permCoinLen_le (two_mul_sq_le_length_encInstance G₀ G₁)
  have hnM : n ≤ (encInstance G₀ G₁).length := le_length_encInstance G₀ G₁
  -- the block sampler `(π', b', r) ↦ ((samplePerm π', b'), r)` against the identity; the
  -- expected type is left to Lean (an ascription makes the elaborator's higher-order
  -- unification against `StatClose.prod` diverge)
  have hs := ((statClose_samplePerm_long hP').prod (StatClose.refl (fun b : Bool => b))).prod
      (StatClose.refl (fun r : V'.Coins (encInstance G₀ G₁).length => r))
  have hpi := statClose_pi hs n
  have hΨ := pushesUniform_readBlocks (((encInstance G₀ G₁).length + 1) ^ 2)
    (V'.coinLen (encInstance G₀ G₁).length) (encInstance G₀ G₁).length n hnM
  have h3 := (hpi.comp_pushesUniform hΨ).map
    (fun cs : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
      (Option.map (encView V' (encInstance G₀ G₁) z)
        (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n cs)).getD [])
  intro T
  have hT := h3.symm T
  simpa only [sim_ofFn_eq V' G₀ G₁ z hnM] using hT

/-- **The string simulator is close to the real view.** Given the typed closeness of the
truncated simulator (Thm-122.3.trunc, which is where `σ(G₀) = G₁` enters), the encoded view of `V'` in the real
iteration and the output of the string simulator on a tape of `|x| · blockLen V' |x|` bits are
within `2^{-n} + (n + 1) · permFailBound n`.

**Proof sketch.** Three `StatClose` steps joined by `StatClose.trans`: (1) the real view with
the sampled `π` against the real view with a uniform `π` (`statClose_real_ideal`), within
`permFailBound n`; (2) the hypothesis mapped by `v ↦ (Option.map encView v).getD []` and
reversed, within `2^{-n}`; (3) the typed simulator on uniform blocks against the string
simulator (`statClose_typed_string`), within `n · permFailBound n`. -/
theorem statClose_real_sim (V' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n))
    (z : List Bool)
    (hclose : StatClose (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n)
      (fun w => some (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w)) ((2 : ℝ)⁻¹ ^ n))
    (m : ℕ) (hm : m = (encInstance G₀ G₁).length * blockLen V' (encInstance G₀ G₁).length) :
    StatClose
      (fun r : (giProtocol.withV V').ExecCoins giProtocol.P (encInstance G₀ G₁) =>
        ((giProtocol.withV V').viewV (encInstance G₀ G₁) (encPerm σ) z r).encode)
      (fun r : Fin m → Bool => sim V' (encInstance G₀ G₁) z (List.ofFn r))
      ((2 : ℝ)⁻¹ ^ n + ((n : ℝ) + 1) * permFailBound n) := by
  subst hm
  have h1 := statClose_real_ideal V' G₀ G₁ σ z
  have h2 : StatClose
      (fun w : Equiv.Perm (Fin n) × V'.Coins (encInstance G₀ G₁).length =>
        encView V' (encInstance G₀ G₁) z (realView G₀ σ (vstar V' (encInstance G₀ G₁) z) w))
      (fun c : Fin n → (Equiv.Perm (Fin n) × Bool) × V'.Coins (encInstance G₀ G₁).length =>
        (Option.map (encView V' (encInstance G₀ G₁) z)
          (simTrunc G₀ G₁ (vstar V' (encInstance G₀ G₁) z) n c)).getD [])
      ((2 : ℝ)⁻¹ ^ n) :=
    hclose.symm.map fun o => (Option.map (encView V' (encInstance G₀ G₁) z) o).getD []
  have h3 := statClose_typed_string V' G₀ G₁ z
  refine ((h1.trans h2).trans h3).mono (le_of_eq ?_)
  ring

/-- The error bound `2^{-n} + (n + 1) · permFailBound n` at `n = instanceVertices |x|` is
negligible in `|x|` (Inf-4.4).

**Proof sketch.** `2^{-n}` is negligible by `negligible_two_pow_neg_sqrt_div` since
`√(N/4) ≤ instanceVertices N` for `N ≥ 8` (`Nat.sqrt_le_sqrt`, `pow_le_pow_of_le_one`), and
`(n + 1) · permFailBound n ≤ 2 N · permFailBound n` for `N ≥ 1` since `n ≤ N`, which is
negligible by `negligible_mul_permFailBound` (`Negligible.const_mul`, `Negligible.mono`);
conclude by `Negligible.add`. -/
theorem negligible_delta :
    Negligible fun N : ℕ => (2 : ℝ)⁻¹ ^ instanceVertices N +
      ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N) := by
  have h1 : Negligible fun N : ℕ => (2 : ℝ)⁻¹ ^ instanceVertices N := by
    refine (negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mono ⟨8, fun N hN => ?_⟩
    have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have h2 : Negligible fun N : ℕ =>
      ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N) := by
    refine (negligible_mul_permFailBound.const_mul 2).mono ⟨1, fun N hN => ?_⟩
    have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
    have hv' : (instanceVertices N : ℝ) + 1 ≤ 2 * N := by
      have h1 : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
      have h2 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    have hpf : 0 ≤ permFailBound (instanceVertices N) := by
      unfold permFailBound
      positivity
    rw [abs_of_nonneg (mul_nonneg (by positivity) hpf),
      abs_of_nonneg (mul_nonneg (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hpf))]
    calc ((instanceVertices N : ℝ) + 1) * permFailBound (instanceVertices N)
        ≤ 2 * N * permFailBound (instanceVertices N) := mul_le_mul_of_nonneg_right hv' hpf
      _ = 2 * (N * permFailBound (instanceVertices N)) := by ring
  exact h1.add h2

end TCSlib.Cryptography.GIZK
