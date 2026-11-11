/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Eager
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.Planted
import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA.QueryHandler

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bitwise scheme under chosen-plaintext attack

The bitwise scheme of [PS10, p. 103] encrypts an `n`-bit message one bit at a time with a
single-bit scheme (such as the trapdoor scheme of Algorithm 104.3, secure by Theorem 104.4).
Padded to fixed-length ciphertexts (`PublicKeyScheme.padded`), it is a fixed-length scheme with
`n`-bit messages. If the single-bit scheme is secure, the padded bitwise scheme is CPA-secure in
the game of [PS10, Definition 171.5], where the adversary chooses its two messages after seeing
the public key, and hence secure in the adaptive multi-challenge game.

Ensemble security of the bitwise scheme for message pairs fixed in advance
(`BitPublicKeyScheme.SingleBitSecure.bitwise`) is not enough here: there the messages cannot
depend on the public key. The proof below therefore goes back to single-bit security.

## Main results

* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa`: the padded bitwise scheme is
  CPA-secure. Its helpers are `BitwiseCPA.QueryHandler` (the query-recording handler and its
  machine by T1), `BitwiseCPA.Planted` (the planted challenge answer and the final bit) and
  `BitwiseCPA.Eager` (eager challenge coins and readers).
* `BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa`: and adaptively CPA-secure.
* `BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa`: a fixed-length scheme with `n`-bit
  messages and the same key generator is adaptively CPA-secure.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  p. 103 (the bitwise scheme and the hybrid argument); Algorithm 104.3 and Theorem 104.4 (the
  single-bit trapdoor scheme, book pp. 104–105); Definition 171.5 (book p. 171).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal of the bitwise-cpa fill: a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/BitwiseCPA.lean`, with every foreign
non-reducible TCSlib definition its touched declarations use made irreducible from the
namespace's first `open` on (scan: `SealScan.lean`). -/
attribute [local irreducible] _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PolyExpr.eval _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantAns _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantOut _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantTuple _root_.TCSlib.Cryptography.Composability.BitwiseSim.qDin _root_.TCSlib.Cryptography.Composability.BitwiseSim.qDout _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.distAdv _root_.Turing.pairEncode


/-! ### The hybrid argument -/

section BitwiseCPAProof

open ChallengeSim BitwiseSim ProbComp

/-- The tuple of hybrid `j` on the challenge `l = m₀ ‖ m₁`: block `i` encrypts, with the coins
`v_i`, bit `i` of the right message (`l_{n+i}`) if `i < j` and of the left message (`l_i`)
otherwise. -/
private def hybCt (S : BitPublicKeyScheme) (n j : ℕ) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (l : List Bool) : List Bool :=
  PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
    S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false else l.getD i false])
      (v i))

/-- **The hybrid `H_j`** (step 1): sample the keys, `A`'s coins and `n` single-bit encryption
tapes `v`, run `A` against the CPA oracles whose first challenge `⟨m₀, m₁⟩` is answered with the
padded tuple of hybrid `j` (`hybCt`, later challenges repeat it), and output `A`'s bit. -/
private noncomputable def hybGame (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n j : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (ProbComp.sample (Fin n → S.enc.Coins n)).bind fun v =>
  .pure ((chRun (fun mm => padCt (L.eval n)
      (hybCt S n j (pairFstD (S.gen.runAt n [] rg)) v (List.ofFn mm)))
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q
      (pairFstD (S.gen.runAt n [] rg)) r) none).1 0)

/-- The bitwise encryptor on a coin list: the tuple of the single-bit encryptions with the
consecutive coin segments (`bitwise_enc`, `bitwise_enc_runAtL`). -/
private theorem bitwise_runAtL (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (r : List Bool) :
    S.bitwise.enc.runAtL n (pairEncode pk (List.ofFn m)) r =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAtL n (pairEncode pk [m i]) (coinBlock (S.enc.coinLen n) i r)) := by
  rw [BitPublicKeyScheme.bitwise_enc]
  exact BitPublicKeyScheme.bitwise_enc_runAtL S n pk m r

/-- The bitwise encryptor on the coin blocks `v`: the tuple of the single-bit encryptions with
coins `v_i` (`bitwiseEncCoins_ofFn`, `coinBlock_ofFn_coinBlocks`). -/
private theorem bitwise_runAt_blocks (S : BitPublicKeyScheme) (n : ℕ) (pk : List Bool)
    (m : Fin n → Bool) (v : Fin n → S.enc.Coins n) :
    S.bitwise.enc.runAt n (pairEncode pk (List.ofFn m)) (S.bitwiseEncCoins n v) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [m i]) (v i)) := by
  rw [NUPPT.runAt_eq, bitwise_runAtL, BitPublicKeyScheme.bitwiseEncCoins_ofFn]
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  rw [coinBlock_ofFn_coinBlocks, ← NUPPT.runAt_eq]

/-- The selected half of a challenge query, as the list of its `n` bits read from the query. -/
private theorem ofFn_half {k n : ℕ} (hk : k = n) (b : Bool) (mm : Fin (k + k) → Bool) :
    List.ofFn (if b then (FixedLengthScheme.splitHalf mm).2
      else (FixedLengthScheme.splitHalf mm).1) =
      List.ofFn (fun i : Fin n => (List.ofFn mm).getD ((if b then n else 0) + i) false) := by
  subst hk
  apply List.ext_getElem
  · cases b <;> simp
  · intro t h₁ h₂
    have ht : t < k := by cases b <;> simpa using h₂
    cases b
    · simp [FixedLengthScheme.splitHalf_fst, List.getD_eq_getElem?_getD]
      rw [dif_pos (by omega)]
      rfl
    · simp [FixedLengthScheme.splitHalf_snd, List.getD_eq_getElem?_getD]
      exact congrArg mm (Fin.ext (Nat.add_comm _ _))

/-- A list of `n + n` bits is its first and its last `n` bits. -/
private theorem ofFn_getD_split {n : ℕ} (l : List Bool) (hl : l.length = n + n) :
    l = List.ofFn (fun i : Fin n => l.getD i false) ++
      List.ofFn (fun i : Fin n => l.getD (n + i) false) := by
  apply List.ext_getElem
  · simp [hl]
  · intro t h₁ h₂
    rw [List.getElem_append]
    split
    · next h => simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
    · next h =>
      simp only [List.getElem_ofFn, List.length_ofFn] at h ⊢
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      congr 1
      omega

/-- **The ends of the hybrids are the CPA games** (step 1):
`Pr[Ind_b = 1] = Pr[H_{j_b} = 1]` with `j_0 = 0`, `j_1 = n`.

**Proof sketch.** Eager coins (`expect_simulate_indImpl_cpa`); the padded bitwise encryptor pads
the tuple of single-bit encryptions (`padded_enc_runAt`, `bitwise_runAt_blocks`) on the coin
blocks `v` (the bijection `bitwiseEncCoins`, then `coinsCongr`), and bit `i` of the selected
half is `l_{n+i}` for `b = 1` and `l_i` for `b = 0` (`ofFn_half`). -/
private theorem accept_indGame_eq (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q n : ℕ) (b : Bool) :
    accept ((S.bitwise.padded L hL hmsg).indGame .cpa A q b n) =
      accept (hybGame S L hL hmsg A q n (if b then n else 0)) := by
  have hgen : (S.bitwise.padded L hL hmsg).gen = S.gen :=
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S)
  have hk : (S.bitwise.padded L hL hmsg).msgLen.eval n = n := by
    rw [PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
  rw [accept_eq, accept_eq, FixedLengthPKScheme.indGame_eq, hgen]
  unfold hybGame
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun rg => ?_)
  rw [prob_bind, prob_bind]
  refine congrArg _ (funext fun r => ?_)
  rw [prob_bind, prob_bind]
  refine (expect_simulate_indImpl_cpa _ b n _ _
    (fun a : Fin 1 → Bool => ProbComp.prob (.pure (a 0)) (· = true)) _).trans ?_
  rw [← expect_sample_equiv ((S.bitwiseEncCoins n).trans
    (NUPPT.coinsCongr (padded_enc_coins S.bitwise L hL hmsg) n))]
  refine congrArg _ (funext fun v => ?_)
  refine congrArg (fun g => ProbComp.prob (.pure ((chRun g
    (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r)
      none).1 0)) (· = true)) (funext fun mm => ?_)
  rw [padded_enc_runAt, Equiv.trans_apply, NUPPT.coinsCongr_ofFn,
    ofFn_half hk b (cast ((S.bitwise.padded L hL hmsg).indSpec_challengeDom n) mm),
    ofFn_cast ((S.bitwise.padded L hL hmsg).inLens_one n), ← NUPPT.runAt_eq,
    bitwise_runAt_blocks]
  unfold hybCt
  refine congrArg (fun l => padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn l)))
    (funext fun i => ?_)
  cases b <;> simp [i.isLt]

/-- **Planting a bit is resampling a coin block**: the tuple whose block `j` is `Enc(β; re)` and
whose other blocks are those of hybrid `j` with coins `v` is the bitwise tuple of the message
with bit `j` replaced by `β`, with coin block `j` replaced by `re`. -/
private theorem planted_eq (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (β : Bool) (l : List Bool) :
    PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then S.enc.runAt n (pairEncode pk [β]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        S.enc.runAt n (pairEncode pk [if (i : ℕ) < j then l.getD (n + i) false
          else if (i : ℕ) = j then β else l.getD i false]) (Function.update v ⟨j, hj⟩ re i)) := by
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  by_cases h₁ : (i : ℕ) < j
  · have hne : i ≠ ⟨j, hj⟩ := fun h => by rw [h] at h₁; exact lt_irrefl _ h₁
    simp only [h₁, if_true, Function.update_of_ne hne]
  · by_cases h₂ : (i : ℕ) = j
    · have heq : i = ⟨j, hj⟩ := Fin.ext h₂
      subst heq
      simp only [h₁, if_false, if_true, Function.update_self]
    · have hne : i ≠ ⟨j, hj⟩ := fun h => h₂ (by rw [h])
      simp only [h₁, h₂, if_false, Function.update_of_ne hne]

/-- **Hybrids `j` and `j + 1` with coin block `j` resampled** plant `Enc(l_j; re)`
(`t = false`) and `Enc(l_{n+j}; re)` (`t = true`) at block `j` (`planted_eq`). -/
private theorem hybCt_update (S : BitPublicKeyScheme) (n j : ℕ) (hj : j < n) (pk : List Bool)
    (v : Fin n → S.enc.Coins n) (re : S.enc.Coins n) (l : List Bool) (t : Bool) :
    hybCt S n (if t then j + 1 else j) pk (Function.update v ⟨j, hj⟩ re) l =
      PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
        if (i : ℕ) < j then S.enc.runAt n (pairEncode pk [l.getD (n + i) false]) (v i)
        else if (i : ℕ) = j then
          S.enc.runAt n (pairEncode pk [if t then l.getD (n + j) false else l.getD j false]) re
        else S.enc.runAt n (pairEncode pk [l.getD i false]) (v i)) := by
  rw [planted_eq S n j hj]
  unfold hybCt
  refine congrArg (fun l => PrivateKeyScheme.encodeList (List.ofFn l)) (funext fun i => ?_)
  refine congrArg (fun b => S.enc.runAt n (pairEncode pk [b]) (Function.update v ⟨j, hj⟩ re i)) ?_
  rcases lt_trichotomy (i : ℕ) j with h | h | h
  · have h' : (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h, h']
  · cases t <;> simp [h]
  · have h₁ : ¬ (i : ℕ) < j := by omega
    have h₂ : (i : ℕ) ≠ j := by omega
    have h₃ : ¬ (i : ℕ) < j + 1 := by omega
    cases t <;> simp [h₁, h₂, h₃]

/-- The advice length of the reduction's handler: `2n + 2(n + 1)·B(n) + 4`. -/
private def bwLaux (S : BitPublicKeyScheme) : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.mul (.const 2) (.mul (.add .var (.const 1)) S.enc.coins)))
    (.const 4)

/-- The reduction's advice at `n`: `⟨1^{j⋆(n)}, ⟨1^{(j⋆(n)+1)·B(n)}, 0^…⟩⟩`, padded with zeros to
`bwLaux S` bits. -/
private def bwAux (S : BitPublicKeyScheme) (js : ℕ → ℕ) (n : ℕ) : List Bool :=
  pairEncode (List.replicate (js n) true)
    (pairEncode (List.replicate ((js n + 1) * S.enc.coinLen n) true)
      (List.replicate ((bwLaux S).eval n - (2 * js n + 2 * ((js n + 1) * S.enc.coinLen n) + 4))
        false))

/-- The advice has `bwLaux S` bits when `j⋆(n) ≤ n`. -/
private theorem bwAux_length (S : BitPublicKeyScheme) (js : ℕ → ℕ) (hjs : ∀ n, js n ≤ n)
    (n : ℕ) : (bwAux S js n).length = (bwLaux S).eval n := by
  have h := Nat.mul_le_mul_right (S.enc.coinLen n) (Nat.add_le_add_right (hjs n) 1)
  have h' := hjs n
  simp only [bwAux, bwLaux, length_pairEncode, List.length_replicate, PolyExpr.eval_add,
    PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var, ← NUPPT.coinLen_eq]
  omega

/-- **The exact identity of step 3.** Let `D` be the machine of `exists_qHandlerMachine` for the
handler with advice `bwAux S js` (the index `j = j⋆(n)`), answer `plantAns` and final bit
`plantOut`. At `n` with `j < n`, the advantage between the hybrids `H_j` and `H_{j+1}` equals
`D`'s advantage between `⟨pk, Enc_pk(0)⟩` and `⟨pk, Enc_pk(1)⟩`.

**Proof sketch.** Fix `n`, the keys and `A`'s coins. Both hybrids answer `A`'s first challenge
`l = m₀ ‖ m₁` only (`chRun_congr`). On `z = ⟨pk, Enc(β; re)⟩` with seed blocks `v`, `D` runs `A`
answering the planted tuple `W β v re l` (`plantTuple_spec`) and outputs
`(l_j ≠ l_{n+j}) ∧ (a ≠ l_j)` (`plantOut_recorded`), or `0` without a challenge
(`plantOut_init`). Resampling coin block `j` (`expect_sample_update`) turns hybrid `j` into
`W (l_j)` and hybrid `j + 1` into `W (l_{n+j})` (`hybCt_update`), and the case split on
`(l_j, l_{n+j})` (`expect_indicator_sub`) matches the two differences. -/
private theorem hyb_advantage_eq {S : BitPublicKeyScheme} (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) (A : NUPPT) (q : PolyExpr) (js : ℕ → ℕ) (D : NUPPT) (n : ℕ)
    (hj : js n < n)
    (φ : (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) × A.Coins n ≃ D.Coins n)
    (hφ : ∀ (ins outs : Fin 2 → ℕ), (fun i => (qDin L (.add .var .var) i).eval n) = ins →
      (fun i => (qDout (.add .var (.const 1)) L i).eval n) = outs →
      ∀ (z : List Bool) (ω : Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool)
        (r : A.Coins n),
        (∀ y : List Bool, y.length = (PolyExpr.add .var .var).eval n →
          (plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (bwAux S js n) y))).length = L.eval n) →
        D.runAt n z (φ (ω, r)) =
          plantOut (pairEncode (seedIn n z (List.ofFn ω))
            (pairEncode (pairEncode (bwAux S js n)
              ((firstQ (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r)).elim
                (false :: List.replicate ((PolyExpr.add .var .var).eval n) false) (true :: ·)))
              (List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode (seedIn n z (List.ofFn ω))
                  (pairEncode (bwAux S js n) (List.ofFn y))))
                (A.toCompOn (bitCodec ins outs 1) n (q.eval n) (pairFstD z) r) none).1)))) :
    advantage (hybGame S L hL hmsg A (q.eval n) n (js n))
        (hybGame S L hL hmsg A (q.eval n) n (js n + 1)) =
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n) := by
  -- Notation: the game's computation, `A`'s bit, and the planted padded tuple.
  let comp : S.gen.Coins n → A.Coins n →
      OracleComp ((S.bitwise.padded L hL hmsg).indSpec n) (Fin 1 → Bool) := fun rg r =>
    A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
      (pairFstD (S.gen.runAt n [] rg)) r
  let F : S.gen.Coins n → A.Coins n → List Bool → Bool := fun rg r w =>
    (chRun (fun _ => w) (comp rg r) none).1 0
  let W : Bool → S.gen.Coins n → (Fin n → S.enc.Coins n) → S.enc.Coins n → List Bool →
      List Bool := fun β rg v re l =>
    padCt (L.eval n) (PrivateKeyScheme.encodeList (List.ofFn fun i : Fin n =>
      if (i : ℕ) < js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD (n + i) false]) (v i)
      else if (i : ℕ) = js n then
        S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [β]) re
      else S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [l.getD i false]) (v i)))
  -- The handler's lengths are the game's.
  have hins : (fun i => (qDin L (.add .var .var) i).eval n) =
      (S.bitwise.padded L hL hmsg).inLens n := by
    funext i
    match i with
    | 0 => rw [qDin_zero, FixedLengthPKScheme.inLens_zero, PublicKeyScheme.padded_ctLen]
    | 1 =>
      rw [qDin_one, FixedLengthPKScheme.inLens_one, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add]
  have houts : (fun i => (qDout (.add .var (.const 1)) L i).eval n) =
      (S.bitwise.padded L hL hmsg).outLens n := by
    funext i
    match i with
    | 0 =>
      rw [qDout_zero, FixedLengthPKScheme.outLens_zero, PublicKeyScheme.padded_msgLen,
        PolyExpr.eval_add, PolyExpr.eval_const]
    | 1 => rw [qDout_one, FixedLengthPKScheme.outLens_one, PublicKeyScheme.padded_ctLen]
  -- The seed is `n` coin blocks.
  let seedE : (Fin n → S.enc.Coins n) ≃ (Fin ((PolyExpr.mul .var S.enc.coins).eval n) → Bool) :=
    (coinBlocks n (S.enc.coinLen n)).trans
      (Equiv.arrowCongr (finCongr (S.bitwise_enc_coinLen n)) (Equiv.refl Bool))
  have hseed : ∀ v, List.ofFn (seedE v) = List.ofFn (coinBlocks n (S.enc.coinLen n) v) :=
    fun v => (List.ofFn_congr (S.bitwise_enc_coinLen n) _).symm
  have hL' : ∀ (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m))
        re).length + 2 ≤ L.eval n := by
    have h := hL n
    rw [BitPublicKeyScheme.bitwise_gen] at h
    exact h
  -- The handler's answer to a challenge `l` is the planted padded tuple.
  have hans : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (l : List Bool), l.length = n + n →
      plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) l)) = W β rg v re l := by
    intro β rg re v l hl
    rw [plantAns_eq, BitPublicKeyScheme.pkEncDist_eq, hseed v, bwAux]
    conv_lhs => rw [ofFn_getD_split l hl]
    rw [plantTuple_spec S.enc S.enc_uniform n (js n) hj, seedIn_eq, pairFstD_pairEncode,
      pairFstD_pairEncode, List.length_replicate]
  have hw : ∀ (β : Bool) (rg : S.gen.Coins n) (re : S.enc.Coins n) (v : Fin n → S.enc.Coins n)
      (y : List Bool), y.length = (PolyExpr.add .var .var).eval n →
      (plantAns S.enc L (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
        (pairEncode (bwAux S js n) y))).length = L.eval n := by
    intro β rg re v y hy
    rw [PolyExpr.eval_add, PolyExpr.eval_var] at hy
    rw [hans β rg re v y hy]
    show (padCt (L.eval n) _).length = L.eval n
    refine length_padCt ?_
    rw [planted_eq S n (js n) hj, ← bitwise_runAt_blocks]
    exact hL' rg _ _
  -- Step 3, distinguisher side: `D`'s verdict.
  have hpt : ∀ (β : Bool) (rg : S.gen.Coins n) (r : A.Coins n) (re : S.enc.Coins n)
      (v : Fin n → S.enc.Coins n),
      D.distinguisherL n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        (firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false) := by
    intro β rg r re v
    have hz : pairFstD (S.pkEncDist n β (rg, re)) = pairFstD (S.gen.runAt n [] rg) := by
      rw [BitPublicKeyScheme.pkEncDist_eq, pairFstD_pairEncode]
    have ha : List.ofFn (chRun (fun y => plantAns S.enc L (pairEncode
        (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) (List.ofFn y))))
        (A.toCompOn ((S.bitwise.padded L hL hmsg).indCodec n) n (q.eval n)
          (pairFstD (S.gen.runAt n [] rg)) r) none).1 =
        [F rg r ((firstQ (comp rg r)).elim [] fun l => plantAns S.enc L (pairEncode
          (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
            (pairEncode (bwAux S js n) l)))] := by
      rw [chRun_congr _ (fun _ => (firstQ (comp rg r)).elim [] fun l => plantAns S.enc L
        (pairEncode (seedIn n (S.pkEncDist n β (rg, re)) (List.ofFn (seedE v)))
          (pairEncode (bwAux S js n) l))) _ fun mm hmm => by rw [hmm, Option.elim_some],
        List.ofFn_succ, List.ofFn_zero]
    have hrun : D.runAt n (S.pkEncDist n β (rg, re)) (φ (seedE v, r)) =
        [(firstQ (comp rg r)).elim false fun l =>
          (l.getD (js n) false != l.getD (n + js n) false) &&
            (F rg r (W β rg v re l) != l.getD (js n) false)] := by
      rw [hφ _ _ hins houts _ _ _ (hw β rg re v), hz, ← indCodec_eq_bitCodec, ha]
      cases hq : firstQ (comp rg r) with
      | none => simp only [Option.elim_none, plantOut_init]
      | some l =>
        have hl : l.length = n + n := by
          rw [length_of_firstQ_eq_some _ hq, FixedLengthPKScheme.inLens_one,
            PublicKeyScheme.padded_msgLen, PolyExpr.eval_var]
        simp only [Option.elim_some]
        rw [hans β rg re v l hl, bwAux, plantOut_recorded, List.headD_cons]
    rw [NUPPT.distinguisherL_eq, hrun]
    generalize ((firstQ (comp rg r)).elim false fun l =>
      (l.getD (js n) false != l.getD (n + js n) false) &&
        (F rg r (W β rg v re l) != l.getD (js n) false)) = x
    cases x <;> rfl
  have hD : ∀ β : Bool, acceptProb (S.pkEncDist n β) (D.distinguisherL n) =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            expect (ProbComp.sample (S.enc.Coins n)) fun re =>
              if ((firstQ (comp rg r)).elim false fun l =>
                (l.getD (js n) false != l.getD (n + js n) false) &&
                  (F rg r (W β rg v re l) != l.getD (js n) false)) = true then 1 else 0 := by
    intro β
    rw [Bridge.acceptProb_eq, accept_eq, Bridge.acceptGame_eq, prob_bind, expect_sample_prod]
    refine congrArg _ (funext fun rg => ?_)
    simp only [prob_bind, prob_pure]
    rw [expect_sample_comm, ← expect_sample_equiv φ, expect_sample_prod, expect_sample_comm]
    refine congrArg _ (funext fun r => ?_)
    rw [← expect_sample_equiv seedE]
    refine congrArg _ (funext fun v => congrArg _ (funext fun re => ?_))
    rw [hpt β rg r re v]
  -- Step 3, hybrid side: only the first challenge matters.
  have hH : ∀ j' : ℕ, accept (hybGame S L hL hmsg A (q.eval n) n j') =
      expect (ProbComp.sample (S.gen.Coins n)) fun rg =>
        expect (ProbComp.sample (A.Coins n)) fun r =>
          expect (ProbComp.sample (Fin n → S.enc.Coins n)) fun v =>
            if F rg r ((firstQ (comp rg r)).elim [] fun l =>
              padCt (L.eval n) (hybCt S n j' (pairFstD (S.gen.runAt n [] rg)) v l)) = true
            then 1 else 0 := by
    intro j'
    rw [accept_eq]
    unfold hybGame
    rw [prob_bind]
    refine congrArg _ (funext fun rg => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [prob_bind]
    refine congrArg _ (funext fun v => ?_)
    rw [prob_pure]
    congr 2
    exact congrArg (fun p : (Fin 1 → Bool) ×
        Option (Fin ((S.bitwise.padded L hL hmsg).outLens n 1) → Bool) => p.1 0)
      (chRun_congr _ _ _ fun mm hmm => by rw [hmm, Option.elim_some])
  -- Assemble: both differences are `𝔼_{rg, r}` of equal pointwise differences.
  rw [advantage_eq, distAdv_def, hH (js n), hH (js n + 1), hD false, hD true]
  congr 1
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun rg => ?_)
  rw [← expect_sub]
  conv_rhs => rw [← expect_sub]
  refine congrArg _ (funext fun r => ?_)
  cases hq : firstQ (comp rg r) with
  | none => simp only [Option.elim_none, Bool.false_eq_true, if_false, sub_self]
  | some l =>
    simp only [Option.elim_some]
    rw [← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0),
      ← expect_sample_update (⟨js n, hj⟩ : Fin n) (fun v => if F rg r (padCt (L.eval n)
        (hybCt S n (js n + 1) (pairFstD (S.gen.runAt n [] rg)) v l)) = true then (1 : ℝ) else 0)]
    have h₀ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l false
    have h₁ := fun v re =>
      hybCt_update S n (js n) hj (pairFstD (S.gen.runAt n [] rg)) v re l true
    simp only [Bool.false_eq_true, if_false, if_true] at h₀ h₁
    simp only [h₀, h₁]
    have key := expect_indicator_sub (ρ := (Fin n → S.enc.Coins n) × S.enc.Coins n)
      (fun β p => F rg r (W β rg p.1 p.2 l)) (l.getD (js n) false) (l.getD (n + js n) false)
    rw [expect_sample_prod, expect_sample_prod, expect_sample_prod, expect_sample_prod] at key
    exact key

end BitwiseCPAProof

/-- **The padded bitwise scheme is CPA-secure** when its single-bit scheme is secure
[PS10, the hybrid argument of p. 103, in the CPA game of Definition 171.5]. The bound `hL`
covers every ciphertext of the bitwise scheme, so `S.bitwise.padded L hL hmsg` has `n`-bit
messages and `L(n)`-bit ciphertexts.

**Proof sketch.**
1. Fix `A` and `q`. For `j ≤ n` let `H_j` be the CPA experiment whose challenge encrypts, bit by
   bit with independent coins `v_i`, the first `j` bits of the right message and the remaining
   bits of the left message (`hybGame`, with the encryption coins sampled in advance). `H_0` and
   `H_n` have the acceptance probabilities of the experiments with `b = false` and `b = true`
   (`accept_indGame_eq`: eager coins `BitwiseSim.expect_simulate_indImpl_cpa`, the bitwise
   layout `bitwise_enc_runAtL` and the coin blocks `bitwiseEncCoins_ofFn`).
2. By `Games.exists_advantage_hybrid_gap`, at each `n > 0` some `j⋆(n) < n` has
   `advantage(H_{j⋆}, H_{j⋆+1}) ≥ advantage(H_0, H_n) / n`; at `n = 0` the two ends coincide and
   the advantage is `0`.
3. The distinguisher `D` on `⟨pk, c⟩` runs `A` on `pk`, answers every `Dec` query with `⊥`, answers
   the first challenge `⟨m₀, m₁⟩` (and every later one) with the padded bitwise ciphertext whose
   block `j⋆` is `c` and whose other blocks it encrypts itself (bits of `m₁` before `j⋆`, of `m₀`
   after) on `pk` and its seed of `n` single-bit encryption tapes (`BitwiseSim.plantAns`), and
   outputs `A`'s bit, flipped when `(m₀_{j⋆}, m₁_{j⋆}) = (1, 0)` and replaced by `0` when the two
   bits agree or no challenge was asked (`BitwiseSim.plantOut`). `D` is a machine by T1 for the
   query-recording handler with `j⋆(n)` in its initial state (`BitwiseSim.exists_qHandlerMachine`).
   Then `advantage(H_{j⋆}, H_{j⋆+1})` equals `D`'s single-bit advantage between `⟨pk, Enc_pk(0)⟩`
   and `⟨pk, Enc_pk(1)⟩` exactly (`hyb_advantage_eq`): only the first challenge matters
   (`ChallengeSim.chRun_congr`); resampling coin block `j⋆` turns the two hybrids into the
   planted tuples with `Enc(m₀_{j⋆})` and `Enc(m₁_{j⋆})` (`BitwiseSim.expect_sample_update`); and
   the signed case split on `(m₀_{j⋆}, m₁_{j⋆})` is `ChallengeSim.expect_indicator_sub`.
4. So `A`'s advantage is at most `n` times `D`'s advantage, negligible by `singleBitSecure_iff`;
   the product is negligible by `Negligible.polyExpr_mul` with `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).INDSecure .cpa := by
  rw [FixedLengthPKScheme.INDSecure_iff]
  intro A q
  -- Steps 1–2: the hybrids and, for `n > 0`, an index `j⋆(n) < n` of a largest gap.
  have hgap : ∀ n, ∃ j ≤ n, 0 < n → j < n ∧
      advantage (hybGame S L hL hmsg A (q.eval n) n 0) (hybGame S L hL hmsg A (q.eval n) n n) /
          n ≤
        advantage (hybGame S L hL hmsg A (q.eval n) n j)
          (hybGame S L hL hmsg A (q.eval n) n (j + 1)) := by
    intro n
    by_cases hn : 0 < n
    · obtain ⟨j, hj, hgj⟩ := exists_advantage_hybrid_gap (hybGame S L hL hmsg A (q.eval n) n) hn
      exact ⟨j, hj.le, fun _ => ⟨hj, hgj⟩⟩
    · exact ⟨0, Nat.zero_le _, fun h => absurd h hn⟩
  choose js hjle hjs using hgap
  -- Step 2: the distinguisher `D`, by T1 for the query-recording handler.
  obtain ⟨D, hD⟩ := BitwiseSim.exists_qHandlerMachine A q L (.add .var .var) (.add .var (.const 1))
    (bwLaux S) (.mul .var S.enc.coins) (bwAux S js) (bwAux_length S js hjle)
    (BitwiseSim.plantAns S.enc L) (BitwiseSim.polyTimeComputable_plantAns S.enc L)
    BitwiseSim.plantOut BitwiseSim.polyTimeComputable_plantOut
  refine ⟨fun n => (PolyExpr.var.eval n : ℝ) *
      distAdv (S.pkEncDist n false) (S.pkEncDist n true) (D.distinguisherL n),
    ((BitPublicKeyScheme.singleBitSecure_iff S).1 h D).polyExpr_mul .var, fun n => ?_⟩
  -- Step 1: the ends of the hybrids are the two games.
  rw [advantage_eq, accept_indGame_eq, accept_indGame_eq, ← advantage_eq]
  simp only [Bool.false_eq_true, ↓reduceIte, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [advantage_eq, sub_self, abs_zero, Nat.cast_zero, zero_mul]
  · -- Steps 3–4: the exact identity and the bound `n · ε(n)`.
    obtain ⟨φ, hφ⟩ := hD n
    rw [← hyb_advantage_eq L hL hmsg A q js D n (hjs n hn).1 φ hφ]
    have h1 := (hjs n hn).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn'] at h1
    linarith

/-- **The padded bitwise scheme is adaptively CPA-secure** when its single-bit scheme is secure:
`bitwise_padded_cpa` followed by the hybrid lifting
`Composability.FixedLengthPKScheme.INDSecure.adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) (L : PolyExpr)
    (hL : ∀ n (rg : S.bitwise.gen.Coins n) (m : Fin n → Bool) (re : S.bitwise.enc.Coins n),
      2 * (S.bitwise.enc.runAt n (pairEncode (pairFstD (S.bitwise.gen.runAt n [] rg))
        (List.ofFn m)) re).length + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : (S.bitwise.padded L hL hmsg).AdaptiveINDSecure .cpa :=
  (h.bitwise_padded_cpa L hL hmsg).adaptive_cpa

/-- **A secure single-bit scheme yields an adaptively CPA-secure scheme with `n`-bit messages**:
some fixed-length scheme with message length `PolyExpr.var` and the same key generator is
secure in the adaptive multi-challenge CPA game. The padding bound comes from
`PublicKeyScheme.exists_padBound`.

**Proof sketch.** Take `L`, `hL` and `hmsg` from `S.bitwise.exists_padBound`; the witness is
`S.bitwise.padded L hL hmsg` (`PublicKeyScheme.padded_msgLen`, `PublicKeyScheme.padded_gen`, and
the generator of `S.bitwise` is `S.gen`), secure by `bitwise_padded_adaptive_cpa`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
    {S : BitPublicKeyScheme} (h : S.SingleBitSecure) :
    ∃ S' : FixedLengthPKScheme, S'.msgLen = .var ∧ S'.gen = S.gen ∧
      S'.AdaptiveINDSecure .cpa := by
  obtain ⟨L, hL, hmsg⟩ := S.bitwise.exists_padBound
  exact ⟨S.bitwise.padded L hL hmsg, PublicKeyScheme.padded_msgLen _ _ _ _,
    (PublicKeyScheme.padded_gen _ _ _ _).trans (BitPublicKeyScheme.bitwise_gen S),
    h.bitwise_padded_adaptive_cpa L hL hmsg⟩

end TCSlib.Cryptography.Composability
