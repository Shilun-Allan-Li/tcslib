/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.BlockEncryptor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Proof infrastructure for public-key encryption

The machine-level and combinatorial lemmas behind the theorems of
`TCSlib.Cryptography.Asymptotic.PublicKey` [PS10, §3.10]: the single ⇒ multi-message theorem
for public-key encryption and the bitwise theorem (p. 103) are hybrid arguments whose
reductions encrypt the other positions of the tuple themselves under the public key; Theorem
104.4 reduces a ciphertext distinguisher to a predictor of the hard-core bit. This file provides

* the blockwise coin bijection `coinBlocks` (`({0,1}^B)^k ≃ {0,1}^{k·B}`) and the
  identities relating it to the consecutive coin segments `coinBlock` read by the block
  encryptor;
* the unfolding `blockEncFun_flatten` of the block encryptor of a uniform machine on the
  concatenation of `k` messages of `L(n)` bits, and the splitting `encodeList_ofFn_split`
  of a tuple encoding at a position;
* **the hybrid machine** `exists_hybridMachine`: a non-uniform PPT `B` with coins
  `K · Enc.coins + D.coins` which, on a sample `⟨pk, c⟩`, encrypts the hard-wired messages
  `m'_0, …, m'_{j-1}` and `m_{j+1}, …, m_{K-1}` under `pk` with its own coins (`blockEncFun`,
  `L(n)`-bit blocks), plants `c` at position `j` and runs `D` — the "we can efficiently
  generate encryptions of any message, without knowing the secret key" step of
  [PS10, p. 103], with the hybrid index, the messages and the unary coin offsets in the
  advice (`NUPPT.exists_comp`, `exists_withAdvice`, `exists_split`);
* **the predictor machine** `tdpPredictor` of [PS10, Theorem 104.4, proof]: on `⟨i, y⟩` it
  draws a bit `c`, runs `D` on `⟨i, ⟨y, [c]⟩⟩` and outputs `c ⊕ ¬verdict ⊕ flip`, with the
  coin bijection `predCoins` and the probability identity `uprob_tdpPredictor`;
* the concrete shared-parameter hybrid bound `distAdv_tuple_le_sum` (the content of
  `distAdv_multi_le_sum`), the samplers `singleDist`/`multiDist` and the single-machine hybrid
  bound `exists_hybridBound`;
* glue: `acceptProb_distinguisherL_coins` (a machine's acceptance probability through a
  bijection of its coins), `abs_uexp_sub_le` (averages of pointwise close functions) and the
  averaging identities `uexp_half_add`/`uexp_half_sub` of the prediction lemma.

## Main definitions

* `TCSlib.Cryptography.coinBlocks` — the blockwise coin bijection;
  `TCSlib.Cryptography.hybridCoins` — the coins of a hybrid machine as blocks plus `D`'s coins.
* `TCSlib.Cryptography.hybridPre` — the pre-processing of the hybrid machine;
  `TCSlib.Cryptography.singleDist`, `multiDist`, `hybridAdv` — the samplers of the
  public-key experiments and the planting distinguisher.
* `TCSlib.Cryptography.tdpPredFun`, `tdpPredictor`, `predCoins` — the predictor machine of
  Theorem 104.4 and its coin bijection.

## Main results

* `TCSlib.Cryptography.coinBlock_ofFn_coinBlocks`, `coinBlock_take`, `coinBlock_drop` — coin
  segments of flattened, truncated and shifted coin strings.
* `TCSlib.Cryptography.blockList_flatten`, `blockEncFun_flatten` — the block encryptor on a
  tuple of messages.
* `TCSlib.Cryptography.ofFn_eq_append_cons`, `encodeList_ofFn_split` — splitting a tuple at a
  position.
* `TCSlib.Cryptography.distAdv_tuple_le_sum`, `distAdv_tuple_le_mul` — the concrete hybrid
  bound with a shared public parameter.
* `TCSlib.Cryptography.exists_hybridMachine`, `exists_hybridBound` — the hybrid machine of the
  single ⇒ multi-message and bitwise theorems and the resulting bound `K(n) · ε`.
* `TCSlib.Cryptography.tdpPredictor_runAtL`, `uprob_tdpPredictor` — the predictor machine.
* `TCSlib.Cryptography.acceptProb_distinguisherL_coins`, `abs_uexp_sub_le`, `uexp_half_add`,
  `uexp_half_sub`, `ofFn_fin_one` — glue.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.10, p. 103; Theorem 104.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Theorem 3.2 (the predictor from a distinguisher).
-/

namespace TCSlib.Cryptography

open Complexity Turing
open PrivateKeyScheme (encodeList)

/-! ## Coin blocks -/

/-- The blockwise coin bijection `({0,1}^B)^k ≃ {0,1}^{k·B}`: block `i` occupies the positions
`i·B, …, i·B + B − 1` (`finProdFinEquiv`, `Equiv.curry`). -/
def coinBlocks (k B : ℕ) : (Fin k → Fin B → Bool) ≃ (Fin (k * B) → Bool) :=
  (Equiv.curry _ _ _).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Unfolding of `coinBlocks`: bit `x` is bit `x mod B` of block `x / B`. -/
theorem coinBlocks_apply (k B : ℕ) (v : Fin k → Fin B → Bool) (x : Fin (k * B)) :
    coinBlocks k B v x = v (finProdFinEquiv.symm x).1 (finProdFinEquiv.symm x).2 := rfl

/-- The `i`-th coin segment (`coinBlock`) of the flattening of `v` is the block `v i`.

**Proof sketch.** `List.ext_getElem`: both sides have length `B` (`i < k`), and position `t` of
the segment is bit `i·B + t` of the flat string, which is `finProdFinEquiv (i, t)`
(`finProdFinEquiv_apply_val`), so `coinBlocks_apply` and `Equiv.symm_apply_apply` give
`v i t`. -/
theorem coinBlock_ofFn_coinBlocks (k B : ℕ) (v : Fin k → Fin B → Bool) (i : Fin k) :
    coinBlock B i (List.ofFn (coinBlocks k B v)) = List.ofFn (v i) := by
  have hle : (i : ℕ) * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B i.isLt
    rw [Nat.succ_mul] at this
    exact this
  have key : ∀ (x : Fin (k * B)) (t : ℕ) (ht : t < B), (x : ℕ) = (i : ℕ) * B + t →
      coinBlocks k B v x = v i ⟨t, ht⟩ := by
    intro x t ht hx
    have hx' : x = finProdFinEquiv (i, ⟨t, ht⟩) := by
      apply Fin.ext
      rw [hx, finProdFinEquiv_apply_val]
      ring
    rw [hx', coinBlocks_apply, Equiv.symm_apply_apply]
  apply List.ext_getElem
  · simp only [coinBlock, List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro t h1 h2
    simp only [coinBlock, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    rw [List.length_ofFn] at h2
    exact key _ t h2 (by simp)

/-- A segment below the cut of a truncated coin string is the segment of the string. -/
theorem coinBlock_take (B i k : ℕ) (r : List Bool) (h : i < k) :
    coinBlock B i (r.take (k * B)) = coinBlock B i r := by
  have hle : i * B + B ≤ k * B := by
    have := Nat.mul_le_mul_right B h
    rw [Nat.succ_mul] at this
    exact this
  simp only [coinBlock, List.drop_take, List.take_take]
  congr 1
  omega

/-- A segment of a coin string shifted by `k` blocks is the segment `k + i` of the string. -/
theorem coinBlock_drop (B i k : ℕ) (r : List Bool) :
    coinBlock B i (r.drop (k * B)) = coinBlock B (k + i) r := by
  simp only [coinBlock, List.drop_drop]
  congr 2
  ring

/-- The length of the concatenation of `j` strings of `L` bits. -/
theorem length_flatten_ofFn {L : ℕ} : ∀ (j : ℕ) (f : Fin j → Fin L → Bool),
    (List.ofFn fun i => List.ofFn (f i)).flatten.length = j * L
  | 0, _ => by simp
  | j + 1, f => by
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, List.length_ofFn,
      length_flatten_ofFn j (fun i => f i.succ)]
    ring

/-! ## The block encryptor on a tuple of messages -/

/-- `blockList` with `L`-bit blocks (`0 < L`) and enough fuel on the concatenation of `j`
strings of `L` bits is the list of their `j` encryptions with the consecutive coin segments
(the `L`-bit analogue of `blockList_ofFn`).

**Proof sketch.** Induction on `j`; `List.ofFn_succ` and `List.flatten_cons` split off the
first string, which is nonempty (`0 < L`) so the step fires, `List.take_left'`/`drop_left'`
cut it off exactly, and the segments of `r.drop B` are the shifted segments of `r`
(`List.drop_drop`). -/
theorem blockList_flatten (E : List Bool → List Bool) (L B : ℕ) (hL : 0 < L) (u pk : List Bool) :
    ∀ (j : ℕ) (msg : Fin j → Fin L → Bool) (r : List Bool) (k : ℕ), j ≤ k →
      blockList E L B u pk k (List.ofFn fun i => List.ofFn (msg i)).flatten r =
        List.ofFn fun i : Fin j =>
          E (NUPPT.layout u (pairEncode pk (List.ofFn (msg i))) [] (coinBlock B i r)) := by
  intro j
  induction j with
  | zero =>
    intro msg r k _
    cases k <;> simp [blockList]
  | succ j ih =>
    intro msg r k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons]
    have hne : List.ofFn (msg 0) ++ (List.ofFn fun i => List.ofFn (msg i.succ)).flatten ≠ [] := by
      intro h
      have := congrArg List.length h
      rw [List.length_append, List.length_ofFn, List.length_nil] at this
      omega
    simp only [blockList, hne, if_false, List.cons.injEq]
    rw [List.take_left' (by simp), List.drop_left' (by simp)]
    refine ⟨?_, ?_⟩
    · simp [coinBlock]
    · rw [ih (fun i => msg i.succ) (r.drop B) k (by omega)]
      congr 1
      funext i
      simp only [coinBlock, Fin.val_succ, List.drop_drop]
      rw [show (B + ↑i * B) = (↑i + 1) * B by ring]

/-- **The block encryptor of a uniform machine on a tuple of messages**: on the state
`⟨1^n, ⟨pk, ⟨m_0 ‖ ⋯ ‖ m_{k-1}, r⟩⟩⟩` with `L(n)`-bit messages (`0 < L(n)`) it returns the tuple
of the activations `Enc(1^n, ⟨pk, m_i⟩; r_i)` with the consecutive `B(n)`-coin segments `r_i`
of `r`.

**Proof sketch.** The state word has at least `k` symbols (`0 < L(n)`), so `blockEncFun_spec`
applies with the word length as fuel; `blockList_flatten` lists the `k` block evaluations and
`Uniform.runAtL_eq` identifies each with an activation of `Enc`. -/
theorem blockEncFun_flatten (Enc : NUPPT) (hEnc : Enc.Uniform) (L : PolyExpr) (n : ℕ)
    (hL : 0 < L.eval n) (pk : List Bool) (k : ℕ) (msg : Fin k → Fin (L.eval n) → Bool)
    (r : List Bool) :
    blockEncFun Enc.output L Enc.coins
        (blockState (List.replicate n true) pk (List.ofFn fun i => List.ofFn (msg i)).flatten r) =
      encodeList (List.ofFn fun i : Fin k =>
        Enc.runAtL n (pairEncode pk (List.ofFn (msg i))) (coinBlock (Enc.coinLen n) i r)) := by
  have hk : k ≤ (blockState (List.replicate n true) pk
      (List.ofFn fun i => List.ofFn (msg i)).flatten r).length := by
    simp only [blockState, length_pairEncode, length_flatten_ofFn]
    have := Nat.le_mul_of_pos_right k hL
    omega
  unfold blockEncFun
  rw [blockEncFun_spec Enc.output L Enc.coins (List.replicate n true) pk _ _ r (by
    rw [length_flatten_ofFn, List.length_replicate]
    exact Nat.mul_le_mul_right _ hk)]
  simp only [List.length_replicate]
  rw [blockList_flatten Enc.output (L.eval n) (Enc.coins.eval n) hL (List.replicate n true) pk k
    msg r _ (Nat.le_succ_of_le hk)]
  refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [hEnc.runAtL_eq]
  rfl

/-! ## Splitting a tuple at a position -/

/-- Splitting `List.ofFn F` at position `j`: the first `j` entries, the entry `j`, the rest
(`List.ext_getElem` with `List.getElem_append`, `List.getElem_cons`). -/
theorem ofFn_eq_append_cons {α : Type*} {N : ℕ} (F : Fin N → α) (j : Fin N) :
    List.ofFn F = (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
      F j :: List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_ofFn, List.length_append, List.length_cons]
    omega
  · intro t h1 h2
    rw [List.getElem_append]
    simp only [List.length_ofFn]
    split_ifs with h
    · simp only [List.getElem_ofFn]
      congr 1
    · rw [List.getElem_cons]
      split_ifs with h'
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)
      · simp only [List.getElem_ofFn]
        congr 1
        exact Fin.ext (by dsimp only; omega)

/-- The tuple encoding of `List.ofFn F` split at position `j`: the encoding of the first `j`
entries, then the block `⟨F j, ·⟩` around the encoding of the rest
(`encodeList_eq_flatMap`, `pairEncode_nil_append`). -/
theorem encodeList_ofFn_split {N : ℕ} (F : Fin N → List Bool) (j : Fin N) :
    encodeList (List.ofFn F) =
      encodeList (List.ofFn fun i : Fin j => F (Fin.castLE j.2.le i)) ++
        pairEncode (F j)
          (encodeList (List.ofFn fun i : Fin (N - j - 1) => F ⟨j + 1 + i, by omega⟩)) := by
  rw [ofFn_eq_append_cons F j, encodeList_eq_flatMap, List.flatMap_append, List.flatMap_cons,
    pairEncode_nil_append, ← encodeList_eq_flatMap, ← encodeList_eq_flatMap]

/-! ## The hybrid machine -/

/-- The pre-processing of the hybrid machine on the argument
`y = ⟨⟨⟨pk, c⟩, w⟩, ⟨u, ⟨⟨u₁, u₂⟩, ⟨M₁, M₂⟩⟩⟩⟩` (sample `⟨pk, c⟩`, own coins `w`, advice
`⟨u, …⟩` with `u = 1^n`, `u₁ = 1^{j·B(n)}`, `u₂ = 1^{(j+1)·B(n)}`, `M₁` the first `j` messages and
`M₂` the last `K(n) − j − 1` messages concatenated): encrypt the blocks of `M₁` with the first
`|u₁|` coins of `w` and those of `M₂` with the coins of `w` after the first `|u₂|`
(`blockEncFun`), and return `⟨pk, T₁ ++ ⟨c, T₂⟩⟩`, the tuple with `c` planted at position `j`. -/
def hybridPre (E : List Bool → List Bool) (L B : PolyExpr) (y : List Bool) : List Bool :=
  pairEncode (pairFstD (pairFstD (pairFstD y)))
    (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
        (pairFstD (pairSndD (pairSndD (pairSndD y))))
        ((pairSndD (pairFstD y)).take (pairFstD (pairFstD (pairSndD (pairSndD y)))).length)) ++
      pairEncode (pairSndD (pairFstD (pairFstD y)))
        (blockEncFun E L B (blockState (pairFstD (pairSndD y)) (pairFstD (pairFstD (pairFstD y)))
          (pairSndD (pairSndD (pairSndD (pairSndD y))))
          ((pairSndD (pairFstD y)).drop (pairSndD (pairFstD (pairSndD (pairSndD y)))).length))))

/-- The pre-processing of the hybrid machine is polynomial-time.

**Proof sketch.** Pair projections for the eleven slots, the typed coin cuts
`polyTimeComputable_pairTakePoly`/`pairDropPoly` (`p := var`) on `⟨u₁, w⟩` and `⟨u₂, w⟩` for the
coin segments, `blockEncFun_poly` for the two block encryptors, `PolyTimeComputable.append` and
`pairEncode` for the assembly; the composite equals `hybridPre` by the projection identities. -/
theorem hybridPre_poly {E : List Bool → List Bool} (hE : PolyTimeComputable E) (L B : PolyExpr) :
    PolyTimeComputable (hybridPre E L B) := by
  have hF := polyTimeComputable_pairFstD
  have hS := polyTimeComputable_pairSndD
  have hpk := hF.comp (hF.comp hF)
  have hc := hS.comp (hF.comp hF)
  have hw := hS.comp hF
  have hu := hF.comp hS
  have hrest := hS.comp hS
  have hu₁ := hF.comp (hF.comp hrest)
  have hu₂ := hS.comp (hF.comp hrest)
  have hM₁ := hF.comp (hS.comp hrest)
  have hM₂ := hS.comp (hS.comp hrest)
  have hw₁ := (polyTimeComputable_pairTakePoly .var).comp (hu₁.pairEncode hw)
  have hw₂ := (polyTimeComputable_pairDropPoly .var).comp (hu₂.pairEncode hw)
  have hT₁ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₁.pairEncode hw₁)))
  have hT₂ := (blockEncFun_poly hE L B).comp (hu.pairEncode (hpk.pairEncode (hM₂.pairEncode hw₂)))
  have h := hpk.pairEncode (hT₁.append (hc.pairEncode hT₂))
  convert h using 1
  funext y
  simp only [hybridPre, blockState, Function.comp, pairFstD_pairEncode, pairSndD_pairEncode,
    PolyExpr.eval_var]

/-- **The hybrid machine** of the single ⇒ multi-message and bitwise theorems
[PS10, p. 103]: for a uniform encryptor `Enc`, a distinguisher `D`, a number of positions `K`,
a block length `L`, hybrid indices `j n` and message vectors `m n, m' n`, there is a
non-uniform PPT `B` with coins `K · Enc.coins + D.coins` such that at every parameter `n` with
`j n < K(n)` and `0 < L(n)`, on the sample `⟨pk, c⟩` with coins `v ‖ ρ` (`v` the `K(n)` coin blocks of `Enc`,
`ρ` the coins of `D`), `B` runs `D` on `⟨pk, ⟨c_0, …, c_{K(n)-1}⟩⟩` with coins `ρ`, where
`c_i = Enc(1^n, ⟨pk, m'_i⟩; v_i)` for `i < j`, `c_j = c`, and `c_i = Enc(1^n, ⟨pk, m_i⟩; v_i)`
for `i > j`.

**Proof sketch.** `B` is `D` pre-processed by `hybridPre` (`NUPPT.exists_comp`), with the
advice `⟨1^n, ⟨⟨1^{j·B}, 1^{(j+1)·B}⟩, ⟨M₁, M₂⟩⟩⟩` hard-wired at the parameters with
`j n < K(n)` and empty elsewhere (`NUPPT.exists_withAdvice`; length
at most `2n + 10 + 6·K·B + 3·K·L` by `length_pairEncode` and `length_flatten_ofFn`) and the first
`K · B` coins passed as data (`NUPPT.exists_split`). On the hybrid layout the two block
encryptors unfold by `blockEncFun_flatten`, their coin segments are the blocks of `v`
(`coinBlock_take`, `coinBlock_drop`, `coinBlock_ofFn_coinBlocks`), and the planted tuple is the
split `encodeList_ofFn_split` of the hybrid tuple at `j`. -/
theorem exists_hybridMachine (Enc D : NUPPT) (hEnc : Enc.Uniform) (K L : PolyExpr)
    (j : ℕ → ℕ) (m m' : ∀ n, Fin (K.eval n) → Fin (L.eval n) → Bool) :
    ∃ B : NUPPT, B.coins = .add (.mul K Enc.coins) D.coins ∧
      ∀ n, j n < K.eval n → 0 < L.eval n →
        ∀ (pk c : List Bool) (v : Fin (K.eval n) → Enc.Coins n) (ρ : D.Coins n),
        B.runAtL n (pairEncode pk c)
            (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ) =
          D.runAtL n (pairEncode pk (encodeList (List.ofFn fun i : Fin (K.eval n) =>
            if (i : ℕ) < j n then Enc.runAt n (pairEncode pk (List.ofFn (m' n i))) (v i)
            else if (i : ℕ) = j n then c
            else Enc.runAt n (pairEncode pk (List.ofFn (m n i))) (v i)))) (List.ofFn ρ) := by
  obtain ⟨D₁, hD₁c, -, -, hD₁⟩ :=
    D.exists_comp (hybridPre_poly Enc.polyTimeComputable_output L Enc.coins) polyTimeComputable_id
  let β : ℕ → List Bool := fun n => if hj : j n < K.eval n then pairEncode (List.replicate n true)
    (pairEncode
      (pairEncode (List.replicate (j n * Enc.coinLen n) true)
        (List.replicate ((j n + 1) * Enc.coinLen n) true))
      (pairEncode (List.ofFn fun i : Fin (j n) => List.ofFn (m' n (Fin.castLE hj.le i))).flatten
        (List.ofFn fun i : Fin (K.eval n - j n - 1) =>
          List.ofFn (m n ⟨j n + 1 + i, by omega⟩)).flatten)) else []
  have hβ : ∀ n, (β n).length ≤ (PolyExpr.add (.add (.mul (.const 2) .var) (.const 10))
      (.add (.mul (.const 6) (.mul K Enc.coins)) (.mul (.const 3) (.mul K L)))).eval n := by
    intro n
    by_cases hj : j n < K.eval n
    · simp only [β, dif_pos hj, length_pairEncode, List.length_replicate, length_flatten_ofFn,
        PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, NUPPT.coinLen]
      have h2 : j n * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj.le
      have h3 : (j n + 1) * Enc.coins.eval n ≤ K.eval n * Enc.coins.eval n :=
        Nat.mul_le_mul_right _ hj
      have h4 : j n * L.eval n ≤ K.eval n * L.eval n := Nat.mul_le_mul_right _ hj.le
      have h5 : (K.eval n - j n - 1) * L.eval n ≤ K.eval n * L.eval n :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    · simp [β, dif_neg hj]
  obtain ⟨D₂, hD₂c, hD₂⟩ := D₁.exists_withAdvice β _ hβ
  obtain ⟨B, hBc, -, hB⟩ := D₂.exists_split (.mul K Enc.coins)
  refine ⟨B, by rw [hBc, hD₂c, hD₁c], fun n hj hL pk c v ρ => ?_⟩
  rw [hB, hD₂, hD₁, id_eq]
  have hlen : (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)).length =
      (PolyExpr.mul K Enc.coins).eval n := by
    simp [NUPPT.coinLen]
  rw [List.take_left' hlen, List.drop_left' hlen]
  congr 1
  -- the pre-processing on the hybrid layout
  simp only [hybridPre, β, dif_pos hj, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]
  rw [blockEncFun_flatten Enc hEnc L n hL pk, blockEncFun_flatten Enc hEnc L n hL pk,
    encodeList_ofFn_split _ ⟨j n, hj⟩]
  congr 1
  congr 1
  · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
    have hi : (i : ℕ) < j n := i.isLt
    rw [coinBlock_take _ _ _ _ hi, ← Fin.coe_castLE hj.le i, coinBlock_ofFn_coinBlocks,
      ← NUPPT.runAt_eq]
    simp only [Fin.coe_castLE, hi, if_true]
  · congr 1
    · simp
    · refine congrArg (fun l => encodeList (List.ofFn l)) (funext fun i => ?_)
      have hidx : coinBlock (Enc.coinLen n) (j n + 1 + i)
          (List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v)) =
          List.ofFn (v ⟨j n + 1 + i, by have := i.isLt; omega⟩) :=
        coinBlock_ofFn_coinBlocks (K.eval n) (Enc.coinLen n) v ⟨j n + 1 + i, by have := i.isLt; omega⟩
      rw [coinBlock_drop, hidx, ← NUPPT.runAt_eq]
      simp only [Fin.val_mk]
      rw [if_neg (by omega), if_neg (by omega)]

/-- The coin length of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`. -/
theorem hybridCoins_len (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    K.eval n * Enc.coinLen n + D.coinLen n = B.coinLen n := by
  simp [NUPPT.coinLen, hBc]

/-- The coins of a hybrid machine with coin polynomial `K · Enc.coins + D.coins`: the `K(n)`
coin blocks of `Enc` followed by the coins of `D` (`coinBlocks`, `Fin.appendEquiv`). -/
def hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) :
    (Fin (K.eval n) → Enc.Coins n) × D.Coins n ≃ B.Coins n :=
  ((coinBlocks (K.eval n) (Enc.coinLen n)).prodCongr (Equiv.refl _)).trans
    ((Fin.appendEquiv _ _).trans
      (Equiv.arrowCongr (finCongr (hybridCoins_len B Enc D K n hBc)) (Equiv.refl Bool)))

/-- The coin string of `hybridCoins (v, ρ)` is the flattening of `v` followed by `ρ`
(`List.ofFn_fin_append`, `List.ofFn_congr`). -/
theorem ofFn_hybridCoins (B Enc D : NUPPT) (K : PolyExpr) (n : ℕ)
    (hBc : B.coins = .add (.mul K Enc.coins) D.coins) (v : Fin (K.eval n) → Enc.Coins n)
    (ρ : D.Coins n) :
    List.ofFn (hybridCoins B Enc D K n hBc (v, ρ)) =
      List.ofFn (coinBlocks (K.eval n) (Enc.coinLen n) v) ++ List.ofFn ρ := by
  rw [← List.ofFn_fin_append]
  exact (List.ofFn_congr (hybridCoins_len B Enc D K n hBc)
    (Fin.append (coinBlocks (K.eval n) (Enc.coinLen n) v) ρ)).symm

/-- **A machine's acceptance probability with its coins read through a bijection** `e`: if the
verdict of `B` on `X s` with coins `e t` is `A (X s) t`, the acceptance probabilities of `B`
and `A` on `X` agree (`uprob_comp_equiv` on the coin factor). -/
theorem acceptProb_distinguisherL_coins {σ τ : Type*} [Fintype σ] [Fintype τ] (B : NUPPT)
    (n : ℕ) (X : σ → List Bool) (e : τ ≃ B.Coins n) (A : List Bool → τ → Bool)
    (h : ∀ s t, B.distinguisherL n (X s) (e t) = A (X s) t) :
    acceptProb X (B.distinguisherL n) = acceptProb X A := by
  unfold acceptProb
  rw [← uprob_comp_equiv ((Equiv.refl σ).prodCongr e)]
  congr 1
  funext z
  simp [h]

/-! ## The shared-parameter hybrid bound (concrete) -/

/-- **Planting a single sample into a tuple generated from the adversary's own coins.** If `A` on
`(pk, c pk r)` with coins `(v, r')` is `D` on `(pk, sel pk (update v j r))` with coins `r'`, the
acceptance probability of `A` on the single sample is that of `D` on the full tuple.

**Proof sketch.** Regroup the seeds `(κ × ρ) × ((Fin (q+1) → ρ) × ρ')` as
`ρ × ((Fin (q+1) → ρ) × (κ × ρ'))` and `(κ × (Fin (q+1) → ρ)) × ρ'` as
`(Fin (q+1) → ρ) × (κ × ρ')` (`uprob_comp_equiv`); the event on the left is then
`D (pk, sel pk (update v j r))` and `OneWay.uprob_update` forgets the planted coordinate. -/
private theorem acceptProb_plant {κ π γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (j : Fin (q + 1)) (c : π → ρ → γ)
    (sel : π → (Fin (q + 1) → ρ) → Fin (q + 1) → γ) (D : π × (Fin (q + 1) → γ) → ρ' → Bool)
    (A : π × γ → (Fin (q + 1) → ρ) × ρ' → Bool)
    (hA : ∀ pk r v r', A (pk, c pk r) (v, r') = D (pk, sel pk (Function.update v j r)) r') :
    acceptProb (fun z : κ × ρ => (P z.1, c (P z.1) z.2)) A =
      acceptProb (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, sel (P z.1) z.2)) D := by
  let e₁ : ρ × ((Fin (q + 1) → ρ) × (κ × ρ')) ≃ (κ × ρ) × ((Fin (q + 1) → ρ) × ρ') :=
    { toFun := fun a => ((a.2.2.1, a.1), (a.2.1, a.2.2.2))
      invFun := fun w => (w.1.2, (w.2.1, (w.1.1, w.2.2)))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e₂ : (Fin (q + 1) → ρ) × (κ × ρ') ≃ (κ × (Fin (q + 1) → ρ)) × ρ' :=
    { toFun := fun w => ((w.2.1, w.1), w.2.2)
      invFun := fun z => (z.1.2, (z.1.1, z.2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold acceptProb
  rw [← uprob_comp_equiv e₁, ← uprob_comp_equiv e₂]
  simp only [e₁, e₂, Equiv.coe_fn_mk, hA]
  exact OneWay.uprob_update (ρ := κ × ρ') (α := ρ) j
    (fun u w => D (P w.1, sel (P w.1) u) w.2 = true)

/-- **The hybrid bound with a shared public parameter**, explicit form (the content of
`TCSlib.Cryptography.distAdv_multi_le_sum`): the advantage of `D` between the `q + 1`
encryptions of `m` and of `m'` under one parameter `P k` is at most the sum over `j` of the
advantages, between the single encryptions of `m_j` and `m'_j`, of the distinguisher that
encrypts `m'_0, …, m'_{j-1}` and `m_{j+1}, …, m_q` itself and plants its sample at position `j`.

**Proof sketch.** Hybrids `H_t := ⟨pk, (E pk m'_i r_i)_{i<t}, (E pk m_i r_i)_{i≥t}⟩`, `t ≤ q + 1`,
on the seeds `κ × (Fin (q+1) → ρ)`, `H_0` and `H_{q+1}` the two sides; `abs_sub_le_sum_hybrids`
over `t ∈ range (q+1)` (`Fin.sum_univ_eq_sum_range`). Each gap `|Pr[D(H_j)] − Pr[D(H_{j+1})]|`
is the advantage of the `j`-th planting distinguisher between `⟨pk, E pk m_j r⟩` and
`⟨pk, E pk m'_j r⟩`: `acceptProb_plant` with the selector of `H_j` (resp. `H_{j+1}`), the
coordinate `v j` being replaced by `r` (`Function.update_apply`, the cases `i < j`, `i = j`,
`i > j` of `Fin.lt_def`). -/
theorem distAdv_tuple_le_sum {κ π μ γ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ']
    [Nonempty ρ] {q : ℕ} (P : κ → π) (E : π → μ → ρ → γ) (m m' : Fin (q + 1) → μ)
    (D : π × (Fin (q + 1) → γ) → ρ' → Bool) :
    distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D ≤
    ∑ j : Fin (q + 1), distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
      (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
      (fun (pc : π × γ) (r : (Fin (q + 1) → ρ) × ρ') => D (pc.1, fun i =>
        if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i)) r.2) := by
  -- the hybrid selector: the first `t` positions carry `m'`, the others `m`
  let sel : ℕ → π → (Fin (q + 1) → ρ) → Fin (q + 1) → γ := fun t pk u i =>
    if (i : ℕ) < t then E pk (m' i) (u i) else E pk (m i) (u i)
  let Pr : ℕ → ℝ := fun t =>
    acceptProb (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, sel t (P z.1) z.2)) D
  have h0 : acceptProb (fun z : κ × (Fin (q + 1) → ρ) =>
      (P z.1, fun i => E (P z.1) (m i) (z.2 i))) D = Pr 0 := by
    simp [Pr, sel]
  have hq : acceptProb (fun z : κ × (Fin (q + 1) → ρ) =>
      (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D = Pr (q + 1) := by
    simp [Pr, sel, Fin.is_lt]
  have hstep : ∀ j : Fin (q + 1),
      distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
        (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
        (fun (pc : π × γ) (r : (Fin (q + 1) → ρ) × ρ') => D (pc.1, fun i =>
          if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2 else E pc.1 (m i) (r.1 i))
          r.2) =
      |Pr j - Pr (j + 1)| := by
    intro j
    unfold distAdv
    rw [acceptProb_plant P j (fun pk r => E pk (m j) r) (sel j) D _,
      acceptProb_plant P j (fun pk r => E pk (m' j) r) (sel (j + 1)) D _]
    · intro pk r v r'
      simp only [sel]
      congr 2
      funext i
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        simp [Fin.lt_def, h, hij, Nat.lt_succ_of_lt h]
      · have hij : i = j := Fin.ext h
        subst hij
        simp
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        have h1 : ¬ (i : ℕ) < j := not_lt.mpr h.le
        have h2 : ¬ (i : ℕ) < (j : ℕ) + 1 := not_lt.mpr h
        simp [Fin.lt_def, h1, h2, hij]
    · intro pk r v r'
      simp only [sel]
      congr 2
      funext i
      rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        simp [Fin.lt_def, h, hij]
      · have hij : i = j := Fin.ext h
        subst hij
        simp
      · have hij : i ≠ j := fun hij => by rw [hij] at h; exact lt_irrefl _ h
        have h1 : ¬ (i : ℕ) < j := not_lt.mpr h.le
        simp [Fin.lt_def, h1, hij]
  have hstart : distAdv
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
      (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i))) D =
      |Pr 0 - Pr (q + 1)| := by
    rw [distAdv, h0, hq]
  rw [hstart]
  calc |Pr 0 - Pr (q + 1)|
      ≤ ∑ t ∈ Finset.range (q + 1), |Pr t - Pr (t + 1)| := abs_sub_le_sum_hybrids Pr (q + 1)
    _ = ∑ j : Fin (q + 1), |Pr j - Pr (j + 1)| :=
        (Fin.sum_univ_eq_sum_range (fun t => |Pr t - Pr (t + 1)|) (q + 1)).symm
    _ = _ := Finset.sum_congr rfl fun j _ => (hstep j).symm

/-! ## The samplers of the public-key experiments -/

/-- The single-encryption sampler `{(pk, sk) ← Gen(1^n) : ⟨pk, Enc(1^n, ⟨pk, msg⟩)⟩}` of a key
generator `Gen` and an encryptor `Enc` on the `Lc`-bit message `msg` (the sampler
`PublicKeyScheme.pkEncDist` with its components named). -/
def singleDist (Gen Enc : NUPPT) (n Lc : ℕ) (msg : Fin Lc → Bool) :
    Gen.Coins n × Enc.Coins n → List Bool :=
  fun r => pairEncode (pairFstD (Gen.runAt n [] r.1))
    (Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] r.1)) (List.ofFn msg)) r.2)

/-- The multi-encryption sampler `{(pk, sk) ← Gen(1^n) : ⟨pk, ⟨Enc(1^n, ⟨pk, m_0⟩), …⟩⟩}` on `N`
messages of `Lc` bits with independent encryption coins (the sampler
`PublicKeyScheme.pkMultiEncDist`, and the bitwise scheme's ciphertexts read blockwise). -/
def multiDist (Gen Enc : NUPPT) (n N Lc : ℕ) (m : Fin N → Fin Lc → Bool) :
    Gen.Coins n × (Fin N → Enc.Coins n) → List Bool :=
  fun z => pairEncode (pairFstD (Gen.runAt n [] z.1)) (encodeList (List.ofFn fun i =>
    Enc.runAt n (pairEncode (pairFstD (Gen.runAt n [] z.1)) (List.ofFn (m i))) (z.2 i)))

/-- **The hybrid bound on string samples**: if every planting distinguisher (on the string
sample `⟨pk, c⟩`, with the tuple encoded by `encodeList`) has advantage at most `t` between the
single encryptions of `m_j` and `m'_j`, then `Dst` has advantage at most `N · t` between the
encoded tuples of the `N` encryptions of `m` and of `m'`.

**Proof sketch.** For `N = 0` the two samplers coincide. For `N = q + 1`, `distAdv_tuple_le_sum`
(the encoding moved into `Dst`, `distAdv_comp`) bounds the advantage by the sum of the `q + 1`
planting advantages, each of which is one of the hypotheses after identifying the
`Fin`-indexed with the `ℕ`-indexed branch conditions (`Fin.lt_def`, `Fin.ext_iff`); the sum of
`q + 1` terms `≤ t` is `≤ (q + 1) t`. -/
theorem distAdv_tuple_le_mul {κ ρ ρ' : Type*} [Fintype κ] [Fintype ρ] [Fintype ρ'] [Nonempty ρ]
    {N Lc : ℕ} (P : κ → List Bool) (E : List Bool → (Fin Lc → Bool) → ρ → List Bool)
    (m m' : Fin N → Fin Lc → Bool) (Dst : List Bool → ρ' → Bool) (t : ℝ)
    (ht : ∀ j : Fin N,
      distAdv (fun z : κ × ρ => pairEncode (P z.1) (E (P z.1) (m j) z.2))
        (fun z : κ × ρ => pairEncode (P z.1) (E (P z.1) (m' j) z.2))
        (fun (s : List Bool) (u : (Fin N → ρ) × ρ') =>
          Dst (pairEncode (pairFstD s) (encodeList (List.ofFn fun i : Fin N =>
            if (i : ℕ) < j then E (pairFstD s) (m' i) (u.1 i) else if (i : ℕ) = j then pairSndD s
            else E (pairFstD s) (m i) (u.1 i)))) u.2) ≤ t) :
    distAdv
      (fun z : κ × (Fin N → ρ) =>
        pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m i) (z.2 i))))
      (fun z : κ × (Fin N → ρ) =>
        pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m' i) (z.2 i)))) Dst ≤
      N * t := by
  cases N with
  | zero =>
    have hm : ∀ z : κ × (Fin 0 → ρ),
        (List.ofFn fun i => E (P z.1) (m i) (z.2 i)) = List.ofFn fun i => E (P z.1) (m' i) (z.2 i) :=
      fun z => congrArg List.ofFn (funext fun i => i.elim0)
    simp only [hm, distAdv, sub_self, abs_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ q =>
    have hterm : ∀ j : Fin (q + 1),
        distAdv (fun z : κ × ρ => (P z.1, E (P z.1) (m j) z.2))
          (fun z : κ × ρ => (P z.1, E (P z.1) (m' j) z.2))
          (fun (pc : List Bool × List Bool) (r : (Fin (q + 1) → ρ) × ρ') =>
            (fun w : List Bool × (Fin (q + 1) → List Bool) =>
              fun r' => Dst (pairEncode w.1 (encodeList (List.ofFn w.2))) r')
            (pc.1, fun i => if i < j then E pc.1 (m' i) (r.1 i) else if i = j then pc.2
              else E pc.1 (m i) (r.1 i)) r.2) ≤ t := by
      intro j
      refine le_of_eq_of_le ?_ (ht j)
      unfold distAdv acceptProb
      refine congrArg₂ (fun a b : ℝ => |a - b|) (congrArg uprob (funext fun z => ?_))
        (congrArg uprob (funext fun z => ?_)) <;>
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, Fin.lt_def, Fin.ext_iff]
    calc distAdv
          (fun z : κ × (Fin (q + 1) → ρ) =>
            pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m i) (z.2 i))))
          (fun z : κ × (Fin (q + 1) → ρ) =>
            pairEncode (P z.1) (encodeList (List.ofFn fun i => E (P z.1) (m' i) (z.2 i)))) Dst
        = distAdv (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m i) (z.2 i)))
            (fun z : κ × (Fin (q + 1) → ρ) => (P z.1, fun i => E (P z.1) (m' i) (z.2 i)))
            (fun w r' => Dst (pairEncode w.1 (encodeList (List.ofFn w.2))) r') := rfl
      _ ≤ ∑ j : Fin (q + 1), _ := distAdv_tuple_le_sum P E m m' _
      _ ≤ ∑ _j : Fin (q + 1), t := Finset.sum_le_sum fun j _ => hterm j
      _ = (q + 1 : ℕ) * t := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The `j`-th planting distinguisher of the public-key hybrid argument as a function of the
string sample `⟨pk, c⟩` and typed coins (`N` coin blocks of `Enc`, the coins of `D`): the
behaviour of the hybrid machine `exists_hybridMachine` read through `hybridCoins`. -/
def hybridAdv (Enc D : NUPPT) (n N Lc : ℕ) (m m' : Fin N → Fin Lc → Bool) (j : ℕ) :
    List Bool → (Fin N → Enc.Coins n) × D.Coins n → Bool :=
  fun s u => D.distinguisherL n (pairEncode (pairFstD s) (encodeList (List.ofFn fun i : Fin N =>
    if (i : ℕ) < j then Enc.runAt n (pairEncode (pairFstD s) (List.ofFn (m' i))) (u.1 i)
    else if (i : ℕ) = j then pairSndD s
    else Enc.runAt n (pairEncode (pairFstD s) (List.ofFn (m i))) (u.1 i)))) u.2

/-- **The hybrid bound with a single reduction machine** [PS10, p. 103]: for a key generator
`Gen`, a uniform encryptor `Enc`, a distinguisher `D`, a number of positions `K` and a block
length `L`, and message-vector families `m n, m' n`, there is one non-uniform PPT `B` such that
at every parameter `n`: if `B` distinguishes any two single encryptions of `L(n)`-bit messages
with advantage at most `ε ≥ 0`, then `D` distinguishes the encoded tuples of the `K(n)`
encryptions of `m n` and of `m' n` with advantage at most `K(n) · ε`.

**Proof sketch.** At each `n` with `0 < K(n)` choose the position `j n` maximizing the advantage
of the planting distinguisher `hybridAdv … (j n)` (`Finset.exists_max_image`); the machine `B`
is `exists_hybridMachine` for these positions (hybrid index and messages in the advice). If
`L(n) = 0` the two message vectors coincide and if `K(n) = 0` the two tuples do; otherwise
`distAdv_tuple_le_mul` bounds the advantage by `K(n)` times the maximal planting advantage,
which is the advantage of `B` (`acceptProb_distinguisherL_coins` along `hybridCoins`,
`ofFn_hybridCoins`), hence at most `ε`. -/
theorem exists_hybridBound (Gen Enc D : NUPPT) (hEnc : Enc.Uniform) (K L : PolyExpr)
    (m m' : ∀ n, Fin (K.eval n) → Fin (L.eval n) → Bool) :
    ∃ B : NUPPT, ∀ n (ε : ℝ), 0 ≤ ε →
      (∀ msg msg' : Fin (L.eval n) → Bool,
        distAdv (singleDist Gen Enc n (L.eval n) msg) (singleDist Gen Enc n (L.eval n) msg')
          (B.distinguisherL n) ≤ ε) →
      distAdv (multiDist Gen Enc n (K.eval n) (L.eval n) (m n))
        (multiDist Gen Enc n (K.eval n) (L.eval n) (m' n)) (D.distinguisherL n) ≤ K.eval n * ε := by
  classical
  -- the advantage of the `j`-th planting distinguisher at parameter `n`
  let term : ∀ n, Fin (K.eval n) → ℝ := fun n j =>
    distAdv (singleDist Gen Enc n (L.eval n) (m n j)) (singleDist Gen Enc n (L.eval n) (m' n j))
      (hybridAdv Enc D n (K.eval n) (L.eval n) (m n) (m' n) j)
  -- the maximizing position at each parameter
  have hmax : ∀ n, ∃ j : ℕ, 0 < K.eval n → ∃ hj : j < K.eval n,
      ∀ jf : Fin (K.eval n), term n jf ≤ term n ⟨j, hj⟩ := by
    intro n
    by_cases hK : 0 < K.eval n
    · haveI : Nonempty (Fin (K.eval n)) := ⟨⟨0, hK⟩⟩
      obtain ⟨jf, -, hjf⟩ := Finset.exists_max_image Finset.univ (term n) Finset.univ_nonempty
      exact ⟨jf, fun _ => ⟨jf.isLt, fun j' => hjf j' (Finset.mem_univ _)⟩⟩
    · exact ⟨0, fun h => absurd h hK⟩
  choose jN hjN using hmax
  obtain ⟨B, hBc, hB⟩ := exists_hybridMachine Enc D hEnc K L jN m m'
  refine ⟨B, fun n ε hε hsingle => ?_⟩
  rcases Nat.eq_zero_or_pos (L.eval n) with hL | hL
  · -- no message bits: the two vectors coincide
    have hmm : m n = m' n := funext fun i => funext fun b => absurd b.isLt (by omega)
    rw [hmm, distAdv, sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hε
  rcases Nat.eq_zero_or_pos (K.eval n) with hK | hK
  · -- no positions: the two tuples coincide
    have hmm : ∀ z : Gen.Coins n × (Fin (K.eval n) → Enc.Coins n),
        multiDist Gen Enc n (K.eval n) (L.eval n) (m n) z =
          multiDist Gen Enc n (K.eval n) (L.eval n) (m' n) z := by
      intro z
      simp only [multiDist]
      congr 3
      exact funext fun i => absurd i.isLt (by omega)
    simp only [distAdv, acceptProb, hmm, sub_self, abs_zero, hK, Nat.cast_zero, zero_mul, le_refl]
  obtain ⟨hj, hjmax⟩ := hjN n hK
  -- the maximal planting advantage is the advantage of the machine `B`
  have hmach : ∀ msg : Fin (L.eval n) → Bool,
      acceptProb (singleDist Gen Enc n (L.eval n) msg)
          (hybridAdv Enc D n (K.eval n) (L.eval n) (m n) (m' n) (jN n)) =
        acceptProb (singleDist Gen Enc n (L.eval n) msg) (B.distinguisherL n) := by
    intro msg
    refine (acceptProb_distinguisherL_coins B n _ (hybridCoins B Enc D K n hBc) _ ?_).symm
    rintro ⟨r, s⟩ ⟨v, ρ⟩
    simp only [singleDist, hybridAdv, NUPPT.distinguisherL, NUPPT.runAt_eq, ofFn_hybridCoins,
      hB n hj hL, pairFstD_pairEncode, pairSndD_pairEncode]
  have hbound : term n ⟨jN n, hj⟩ ≤ ε := by
    simp only [term, distAdv, hmach]
    exact hsingle _ _
  calc distAdv (multiDist Gen Enc n (K.eval n) (L.eval n) (m n))
        (multiDist Gen Enc n (K.eval n) (L.eval n) (m' n)) (D.distinguisherL n)
      ≤ K.eval n * term n ⟨jN n, hj⟩ :=
        distAdv_tuple_le_mul (fun r => pairFstD (Gen.runAt n [] r))
          (fun pk msg r => Enc.runAt n (pairEncode pk (List.ofFn msg)) r) (m n) (m' n)
          (D.distinguisherL n) _ (fun j => hjmax j)
    _ ≤ K.eval n * ε := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _)

/-! ## The predictor machine of Theorem 104.4 -/

/-- The raw function of the predictor `A_flip` of [PS10, Theorem 104.4, proof] on the layout
`⟨⟨⟨1^n, ⟨i, y⟩⟩, α⟩, c :: ρ⟩`: run `D` on `⟨1^n, ⟨i, ⟨y, [c]⟩⟩⟩` with advice `α` and coins `ρ`,
and output `[c ⊕ ¬verdict ⊕ flip]` (`c` if `D` accepts, `1 − c` otherwise, negated when `flip`). -/
def tdpPredFun (D : NUPPT) (flip : Bool) (z : List Bool) : List Bool :=
  [xor (xor ((NUPPT.inCoins z).headD false)
    (!decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true]))) flip]

/-- The raw predictor is polynomial-time (`StateLoop.headBit_poly`, `tail_poly`,
`polyTimeComputable_pairEq` for the verdict, `StateLoop.xor_poly`/`not_poly`). -/
theorem tdpPredFun_poly (D : NUPPT) (flip : Bool) : PolyTimeComputable (tdpPredFun D flip) := by
  have hc : PolyTimeComputable fun z => [(NUPPT.inCoins z).headD false] :=
    StateLoop.headBit_poly.comp NUPPT.polyTimeComputable_inCoins
  have hout := D.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
    NUPPT.polyTimeComputable_inParam
    ((polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg).pairEncode
      ((polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg).pairEncode hc))
    NUPPT.polyTimeComputable_inAdvice (StateLoop.tail_poly.comp NUPPT.polyTimeComputable_inCoins))
  have hv : PolyTimeComputable fun z => [decide (D.output (NUPPT.layout (NUPPT.inParam z)
      (pairEncode (pairFstD (NUPPT.inArg z))
        (pairEncode (pairSndD (NUPPT.inArg z)) [(NUPPT.inCoins z).headD false]))
      (NUPPT.inAdvice z) (NUPPT.inCoins z).tail) = [true])] := by
    convert polyTimeComputable_pairEq.comp (hout.pairEncode (polyTimeComputable_const [true]))
      using 1
    funext z
    simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode]
  exact StateLoop.xor_poly (StateLoop.xor_poly hc (StateLoop.not_poly hv))
    (polyTimeComputable_const [flip])

/-- **The predictor machine** `A_flip` of [PS10, Theorem 104.4, proof]: `D`'s advice, coins
`1 + D.coins` (the extra bit `c` first). -/
noncomputable def tdpPredictor (D : NUPPT) (flip : Bool) : NUPPT :=
  NUPPT.ofPolyTime (tdpPredFun_poly D flip) (.add (.const 1) D.coins) D.adv D.advice
    D.advice_length

/-- The coin polynomial of the predictor machine. -/
@[simp] theorem tdpPredictor_coins (D : NUPPT) (flip : Bool) :
    (tdpPredictor D flip).coins = .add (.const 1) D.coins := rfl

/-- Unfolding of the predictor machine: on `⟨i, y⟩` with coins `c :: ρ` it outputs
`[c ⊕ ¬[D(1^n, ⟨i, ⟨y, [c]⟩⟩; ρ) = 1] ⊕ flip]`. -/
theorem tdpPredictor_runAtL (D : NUPPT) (flip : Bool) (n : ℕ) (i y : List Bool) (c : Bool)
    (ρ : List Bool) :
    (tdpPredictor D flip).runAtL n (pairEncode i y) (c :: ρ) =
      [xor (xor c (!decide (D.runAtL n (pairEncode i (pairEncode y [c])) ρ = [true]))) flip] := by
  unfold tdpPredictor
  rw [NUPPT.runAtL_ofPolyTime]
  simp [tdpPredFun, NUPPT.inCoins, NUPPT.inParam, NUPPT.inArg, NUPPT.inAdvice, NUPPT.advInput,
    NUPPT.layout, NUPPT.runAtL]

/-- The coins of the predictor machine: the bit `c` followed by the coins of `D`. -/
def predCoins (D : NUPPT) (flip : Bool) (n : ℕ) :
    Bool × D.Coins n ≃ (tdpPredictor D flip).Coins n :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (Equiv.refl _)).trans
    (Fin.appendEquiv 1 (D.coinLen n))

/-- The coin string of `predCoins (c, ρ)` is `c :: ρ`. -/
theorem ofFn_predCoins (D : NUPPT) (flip : Bool) (n : ℕ) (c : Bool) (ρ : D.Coins n) :
    List.ofFn (predCoins D flip n (c, ρ)) = c :: List.ofFn ρ := by
  show List.ofFn (Fin.append (fun _ : Fin 1 => c) ρ) = c :: List.ofFn ρ
  rw [List.ofFn_fin_append]
  rfl

/-- `if v then c else ¬c` is `c ⊕ ¬v`. -/
theorem ite_eq_xor_not (v c : Bool) : (if v = true then c else !c) = xor c (!v) := by
  cases v <;> cases c <;> rfl

/-- The verdict convention on a one-bit output: `[b] = [true]` iff `b`. -/
theorem decide_singleton_eq_true (b : Bool) : decide ([b] = [true]) = b := by
  cases b <;> rfl

/-- **The prediction experiment of the predictor machine** is the concrete predictor
experiment: over uniform `x` and the coins `c :: ρ`, `A_flip(1^n, ⟨i, enc (f x)⟩) = h x` has the
probability that `(if D(⟨i, ⟨enc (f x), [c]⟩⟩; ρ) then c else ¬c) ⊕ flip = h x`
(`uprob_comp_equiv` along `predCoins`, `tdpPredictor_runAtL`). -/
theorem uprob_tdpPredictor {α : Type*} [Fintype α] (D : NUPPT) (flip : Bool) (n : ℕ)
    (i : List Bool) (f : α → α) (h : α → Bool) (enc : α → List Bool) :
    uprob (fun z : α × (tdpPredictor D flip).Coins n =>
        (tdpPredictor D flip).distinguisherL n (pairEncode i (enc (f z.1))) z.2 = h z.1) =
      uprob (fun z : α × (Bool × D.Coins n) =>
        xor (if D.distinguisherL n (pairEncode i (pairEncode (enc (f z.1)) [z.2.1])) z.2.2
          then z.2.1 else !z.2.1) flip = h z.1) := by
  rw [← uprob_comp_equiv ((Equiv.refl α).prodCongr (predCoins D flip n))]
  congr 1
  funext z
  obtain ⟨x, c, ρ⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, NUPPT.distinguisherL,
    NUPPT.runAt_eq, ofFn_predCoins, tdpPredictor_runAtL, decide_singleton_eq_true, ite_eq_xor_not]

/-! ## Averages and one-letter strings -/

/-- `List.ofFn` of a constant on `Fin 1` is the one-letter string. -/
theorem ofFn_fin_one (b : Bool) : List.ofFn (fun _ : Fin 1 => b) = [b] := by
  simp [List.ofFn_succ]

/-- The average of `1/2 + (a − b)/2` is `1/2 + (E a − E b)/2` (`OneWay.uexp_add`,
`OneWay.uexp_const_mul`, `HardcoreBit.uexp_sub`). -/
theorem uexp_half_add {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 + (a r - b r) / 2) = 1 / 2 + (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 + (a r - b r) / 2) = fun r => 1 / 2 + (1 / 2) * (a r - b r) := by
    funext r; ring
  rw [e, OneWay.uexp_add, OneWay.uexp_const, OneWay.uexp_const_mul, HardcoreBit.uexp_sub]
  ring

/-- The average of `1/2 − (a − b)/2` is `1/2 − (E a − E b)/2`. -/
theorem uexp_half_sub {κ : Type*} [Fintype κ] [Nonempty κ] (a b : κ → ℝ) :
    uexp (fun r => 1 / 2 - (a r - b r) / 2) = 1 / 2 - (uexp a - uexp b) / 2 := by
  have e : (fun r => 1 / 2 - (a r - b r) / 2) = fun r => 1 / 2 + (b r - a r) / 2 := by
    funext r; ring
  rw [e, uexp_half_add]
  ring

/-- Averages of pointwise `c`-close functions are `c`-close (`0 ≤ c` covers the empty type;
copy of the private lemma of `TCSlib.Cryptography.Asymptotic.Sampling`). -/
theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
  rw [← HardcoreBit.uexp_sub]
  unfold uexp
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · rw [h0]
    simpa using hc
  · have hc' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    rw [abs_div, abs_of_pos hc', div_le_iff₀ hc']
    calc |∑ a, (f a - g a)| ≤ ∑ a, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => h a
      _ = c * Fintype.card α := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

end TCSlib.Cryptography
