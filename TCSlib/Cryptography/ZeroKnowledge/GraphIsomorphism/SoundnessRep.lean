/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph non-isomorphism protocol: completeness and soundness

[PS10, Proposition 118.4] for the `|x|`-fold protocol `gniProtocolRep` (Prot-118.3, repeated),
proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`; the main file closes
`gni_interactiveProof` by `exact GI.gni_interactiveProof gniVerifierRep_efficient`.

The verifier's graphs `H_i = σ_i(G_{b_i})` depend only on the number of replies received, so the
transcript against any prover is explicit (`exec_vfirst_eq`): the prover's `i`-th reply is its
next-message function on `[H_0, …, H_i]`. **Completeness** is exact: the honest prover's reply
is `b_i` for every tape (`gni_honest_reply`). **Soundness**: against isomorphic graphs, after
fixing the prover's coins and reading the verifier's tape as the `|x|` blocks
`(b_i, sampler coins_i)` (`gniTapes`), the acceptance event is the adaptive guessing event of
`uprob_gni_rep_cheat` (Lem-119.b) once the `|x|` sampled permutations are replaced by uniform
ones, which costs `|x| · permFailBound n` (`statClose_pi` of `statClose_samplePerm_long`); so
`Pr[accept] ≤ 2^{-|x|} + |x| · permFailBound n`, a negligible function of `|x|`
(`negligible_two_pow_neg`, `negligible_mul_permFailBound`).

## Main definitions

* `TCSlib.Cryptography.GI.blocksEquiv`, `GI.gniTapes` — a tape of `m · c` bits as `m` blocks,
  and the verifier's tape as (bits, sampler coins).

## Main results

* `TCSlib.Cryptography.GI.exec_vfirst_eq` — transcripts of verifier-first protocols whose
  verifier's messages depend only on the number of replies.
* `TCSlib.Cryptography.GI.statClose_pi` — `StatClose` for `m` independent copies.
* `TCSlib.Cryptography.GI.gniRep_complete`, `GI.gniRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErrRep`, `GI.gni_interactiveProof` —
  [PS10, Proposition 118.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Transcripts of verifier-first protocols with history-independent graphs -/

/-- An entry of the list of a tuple below its length (any type). -/
theorem getD_ofFn_lt' {α : Type*} {c : ℕ} (t : Fin c → α) {i : ℕ} (hi : i < c) (d : α) :
    (List.ofFn t).getD i d = t ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

/-- The list of a tuple given by a function on `ℕ` is the map over `List.range`. -/
theorem ofFn_eq_map_range {α : Type*} : ∀ {k : ℕ} (f : Fin k → α) (g : ℕ → α),
    (∀ t : Fin k, f t = g t) → List.ofFn f = List.map g (List.range k)
  | 0, _, _, _ => by simp
  | k + 1, f, g, h => by
    rw [List.ofFn_succ_last, List.range_succ, List.map_append, List.map_singleton,
      ofFn_eq_map_range (fun t => f t.castSucc) g (fun t => by
        show f t.castSucc = g t
        rw [h, Fin.coe_castSucc]), h, Fin.val_last]

/-- In a verifier-first execution of `2k` moves each party has received exactly `k` messages. -/
theorem exec_vfirst_length (P' V : Strategy) (x zP zV rP rV : List Bool) :
    ∀ k, (exec P' V true x zP zV rP rV (2 * k)).1.length = k ∧
      (exec P' V true x zP zV rP rV (2 * k)).2.length = k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : moverIsV true (2 * k) = true := by simp [moverIsV]
    have h2 : moverIsV true (2 * k + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, exec_succ, exec_succ]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false, List.length_append, List.length_singleton]
    omega

/-- **Transcripts against a verifier whose first `m` messages depend only on the number of
replies received.** If `V.next x zV rV hist = Hf hist.length` whenever `hist.length < m`,
then after `2i ≤ 2m` moves of the verifier-first execution the prover has received
`H_0, …, H_{i-1}` and the verifier the replies `P'.next x zP rP [H_0, …, H_j]` for `j < i`.

**Proof sketch.** Induction on `i`: move `2i` is the verifier's (`moverIsV true (2i)`), who sends
`Hf i` on its `i` replies; move `2i + 1` is the prover's, who replies to `[H_0, …, H_i]`
(`List.range_succ`, `List.ofFn_succ_last`). -/
theorem exec_vfirst_eq (P' V : Strategy) (x zP zV rP rV : List Bool) (m : ℕ) (Hf : ℕ → List Bool)
    (hV : ∀ hist : List (List Bool), hist.length < m → V.next x zV rV hist = Hf hist.length) :
    ∀ i ≤ m, exec P' V true x zP zV rP rV (2 * i) =
      (List.map Hf (List.range i),
        List.ofFn fun j : Fin i => P'.next x zP rP (List.map Hf (List.range (j + 1)))) := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have hrec := ih (by omega)
    have h1 : moverIsV true (2 * i) = true := by simp [moverIsV]
    have h2 : moverIsV true (2 * i + 1) = false := by
      simp only [moverIsV_true, decide_eq_false_iff_not]
      omega
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 by ring, exec_succ, exec_succ, hrec]
    simp only [h1, h2, Bool.false_eq_true, if_true, if_false]
    rw [hV _ (by simp; omega)]
    simp only [List.length_ofFn]
    refine Prod.ext ?_ ?_
    · simp [List.range_succ]
    · rw [List.ofFn_succ_last]
      simp only [Fin.coe_castSucc, Fin.val_last, List.range_succ, List.map_append, List.map_singleton]

/-! ### The verdicts of the `|x|`-fold graph non-isomorphism protocol -/

/-- The honest prover's reply on an encoded instance: `decide (¬ G₀ ≅ last graph received)`. -/
theorem gniProver_next_enc {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool)) :
    gniProver.next (encInstance G₀ G₁) y r hist =
      [decide (¬ Isomorphic G₀ (decGraphAt n (hist.getLastD [])))] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (hist.getLastD [])))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold verifier's graph of iteration `|hist|` on an encoded instance, while the
protocol is not over: `σ(G_b)` for the bit `b` and the sampler coins of the coin block.

**Proof sketch.** Unfold the strategy on the branch `|hist| < |x|`, read the two graph words
off the encoded instance (`pairFstD_pairEncode`, `pairSndD_pairEncode`) and transport the vertex
count `instanceVertexCount (encInstance G₀ G₁) = n` (`generalize`/`subst`, then
`decGraphAt_encGraph`). -/
theorem gniVerifierRep_next_lt {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h : hist.length < (encInstance G₀ G₁).length) :
    gniVerifierRep.next (encInstance G₀ G₁) z r hist =
      encGraph (permGraph
        (cond ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false) G₁ G₀)
        (samplePerm n ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).drop 1))) := by
  show (if hist.length < (encInstance G₀ G₁).length then _ else _) = _
  rw [if_pos h]
  show encGraph (permGraph
    (if (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false then
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁)) else
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁))
      ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).drop 1))) = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph]
  cases (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) hist.length r).headD false <;> rfl

/-- The `|x|`-fold verifier's verdict once `|x|` replies are in. -/
theorem gniVerifierRep_next_ge (x z r : List Bool) (hist : List (List Bool)) (h : x.length ≤ hist.length) :
    gniVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        (hist.getD j []).headD false = (coinSlice (1 + (x.length + 1) ^ 2) j r).headD false)] := by
  show (if hist.length < x.length then _ else _) = _
  rw [if_neg (not_lt.2 h)]

/-- The verdict of the `|x|`-fold protocol against a prover `P'`: the verifier's next-message
function on the `2|x|`-move execution. -/
theorem gniProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : gniProtocolRep.ExecCoins P' x) :
    gniProtocolRep.outV P' x y z r =
      gniVerifierRep.next x z (List.ofFn r.2)
        (exec P' gniVerifierRep true x y z (List.ofFn r.1) (List.ofFn r.2) (2 * x.length)).2 := rfl

/-- The graphs of the `|x|`-fold verifier on an encoded instance, as a function of the
iteration index. -/
noncomputable def gniGraphs {n : ℕ} (G₀ G₁ : Graph n) (rV : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph
    (cond ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).headD false) G₁ G₀)
    (samplePerm n ((coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j rV).drop 1)))

/-- The verdict of the `|x|`-fold protocol against `P'` on an encoded instance: every reply's
first bit equals the corresponding bit of the verifier's tape, the `j`-th reply being `P'`'s
next message on the graphs `H_0, …, H_j`. -/
theorem gniRep_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocolRep.outV P' (encInstance G₀ G₁) y z r =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
        (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false)] := by
  rw [gniProtocolRep_outV, exec_vfirst_eq P' gniVerifierRep (encInstance G₀ G₁) y z (List.ofFn r.1)
    (List.ofFn r.2) (encInstance G₀ G₁).length (gniGraphs G₀ G₁ (List.ofFn r.2))
    (fun hist hh => gniVerifierRep_next_lt G₀ G₁ z (List.ofFn r.2) hist hh) _ le_rfl,
    gniVerifierRep_next_ge _ _ _ _ (by simp), wellFormedInstance_encInstance]
  simp only [true_and]
  congr 1
  refine decide_eq_decide.2 (forall_congr' fun j => ?_)
  rw [getD_ofFn_lt' _ j.isLt]

/-- **Completeness of the `|x|`-fold graph non-isomorphism protocol** [PS10, Proposition 118.4]:
on a non-isomorphic encoded instance the honest prover's every reply is the verifier's bit
(`gni_honest_reply`), for every pair of tapes. -/
theorem gniRep_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocolRep.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gniRep_outV_eq]
  have hj : ∀ j : Fin (encInstance G₀ G₁).length,
      (gniProver.next (encInstance G₀ G₁) y (List.ofFn r.1)
        (List.map (gniGraphs G₀ G₁ (List.ofFn r.2)) (List.range (j + 1)))).headD false =
      (coinSlice (1 + ((encInstance G₀ G₁).length + 1) ^ 2) j (List.ofFn r.2)).headD false := by
    intro j
    rw [gniProver_next_enc, List.headD_cons, List.range_succ, List.map_append, List.map_singleton,
      List.getLastD_concat, gniGraphs, decGraphAt_encGraph, gni_honest_reply h]
  simp only [hj, implies_true, decide_true]

/-! ### Tapes as blocks -/

/-- A tape of `m · c` bits as `m` blocks of `c` bits (`finProdFinEquiv`: block `i` occupies
the positions `i c, …, i c + c - 1`). -/
def blocksEquiv (m c : ℕ) : (Fin m → Fin c → Bool) ≃ (Fin (m * c) → Bool) :=
  (Equiv.curry (Fin m) (Fin c) Bool).symm.trans (Equiv.arrowCongr finProdFinEquiv (Equiv.refl Bool))

/-- Entry `k` of the tape of blocks is entry `k mod c` of block `k / c`. -/
theorem blocksEquiv_apply (m c : ℕ) (F : Fin m → Fin c → Bool) (k : Fin (m * c)) :
    blocksEquiv m c F k = F k.divNat k.modNat := by
  simp [blocksEquiv, Equiv.arrowCongr_apply, finProdFinEquiv_symm_apply, Function.uncurry]

/-- Block `j < m` of the tape of blocks is the `j`-th block.

**Proof sketch.** Compare entries (`List.ext_getElem?`): entry `t < c` of the slice is entry
`j c + t` of the tape, which `blocksEquiv_apply` reads as entry `(j c + t) mod c = t` of block
`(j c + t) / c = j`; entries `t ≥ c` are absent on both sides. -/
theorem coinSlice_blocksEquiv (m c : ℕ) (F : Fin m → Fin c → Bool) {j : ℕ} (hj : j < m) :
    coinSlice c j (List.ofFn (blocksEquiv m c F)) = List.ofFn (F ⟨j, hj⟩) := by
  apply List.ext_getElem?
  intro t
  simp only [coinSlice, List.getElem?_take, List.getElem?_drop, List.getElem?_ofFn]
  by_cases ht : t < c
  · have hc : 0 < c := by omega
    have hlt : j * c + t < m * c := by
      calc j * c + t < j * c + c := by omega
        _ = (j + 1) * c := by ring
        _ ≤ m * c := Nat.mul_le_mul_right c hj
    simp only [ht, if_true, hlt, dif_pos, blocksEquiv_apply]
    congr 2
    · apply Fin.ext
      rw [Fin.coe_divNat]
      show (j * c + t) / c = j
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_div_left _ _ hc, Nat.div_eq_of_lt ht, zero_add]
    · apply Fin.ext
      rw [Fin.coe_modNat]
      show (j * c + t) % c = t
      rw [show j * c + t = t + c * j by ring, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  · simp [ht]

/-- The verifier's tape of the `|x|`-fold graph non-isomorphism protocol as the `|x|` bits and
the `|x|` sampler tapes of its coin blocks. -/
def gniTapes (N : ℕ) :
    (Fin N → Bool) × (Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) ≃ gniProtocolRep.V.Coins N :=
  (Equiv.arrowProdEquivProdArrow (Fin N) (fun _ => Bool) (fun _ => Fin (1 * (N + 1) ^ 2) → Bool)).symm.trans
    ((Equiv.piCongrRight fun _ => tapeSplit (1 * (N + 1) ^ 2)).trans (blocksEquiv N (1 + 1 * (N + 1) ^ 2)))

/-- The tape of `gniTapes` is the tape of blocks of the split blocks. -/
theorem gniTapes_apply (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool)) :
    gniTapes N (b, ts) = blocksEquiv N (1 + 1 * (N + 1) ^ 2) (fun j => tapeSplit _ (b j, ts j)) := rfl

/-- Coin block `j < N` of the tape `gniTapes N (b, ts)` is `b_j` followed by the sampler tape
`ts_j`. -/
theorem coinSlice_gniTapes (N : ℕ) (b : Fin N → Bool) (ts : Fin N → (Fin (1 * (N + 1) ^ 2) → Bool))
    {j : ℕ} (hj : j < N) :
    coinSlice (1 + (N + 1) ^ 2) j (List.ofFn (gniTapes N (b, ts))) = b ⟨j, hj⟩ :: List.ofFn (ts ⟨j, hj⟩) := by
  rw [gniTapes_apply, show 1 + (N + 1) ^ 2 = 1 + 1 * (N + 1) ^ 2 by ring, coinSlice_blocksEquiv _ _ _ hj,
    ofFn_tapeSplit]

/-! ### Products of close samplers -/

/-- `m` independent copies of a sampler `δ`-close to uniform are `m δ`-close to uniform.

**Proof sketch.** Induction on `m` through `Fin.consEquiv`: the `m + 1` copies are one copy
and `m` copies (`StatClose.prod`), reassembled by `Fin.cons` (`StatClose.map`); the case `m = 0`
is the equality of two point masses. -/
theorem statClose_pi {σ γ : Type*} [Fintype σ] [Fintype γ] {X : σ → γ} {δ : ℝ}
    (h : StatClose X (id : γ → γ) δ) :
    ∀ m : ℕ, StatClose (fun ts : Fin m → σ => fun k => X (ts k)) (id : (Fin m → γ) → (Fin m → γ)) (m * δ)
  | 0 => by
    intro T
    have h1 : (fun ts : Fin 0 → σ => T (fun k => X (ts k))) = fun _ => T Fin.elim0 := by
      funext ts
      congr 1
      funext k
      exact k.elim0
    have h2 : (fun s : Fin 0 → γ => T (id s)) = fun _ => T Fin.elim0 := by
      funext s
      congr 1
      funext k
      exact k.elim0
    rw [h1, h2]
    simp only [Nat.cast_zero, zero_mul]
    rcases em (T Fin.elim0) with hT | hT
    · simp [hT, uprob_true]
    · simp [hT, uprob_false]
  | m + 1 => by
    have ih := statClose_pi h m
    have hp := (h.prod ih).map (fun q : γ × (Fin m → γ) => (Fin.cons q.1 q.2 : Fin (m + 1) → γ))
    have h1 := (hp.comp_equiv_left (Fin.consEquiv fun _ => σ).symm).comp_equiv_right
      (Fin.consEquiv fun _ => γ).symm
    intro T
    have := h1 T
    have e1 : ∀ ts : Fin (m + 1) → σ,
        (Fin.cons (X (ts 0)) (fun k => X (Fin.tail ts k)) : Fin (m + 1) → γ) = fun k => X (ts k) := by
      intro ts
      funext k
      cases k using Fin.cases with
      | zero => rfl
      | succ k => rfl
    have e2 : ∀ s : Fin (m + 1) → γ, (Fin.cons (s 0) (Fin.tail s) : Fin (m + 1) → γ) = s :=
      fun s => Fin.cons_self_tail s
    simp only [Fin.consEquiv_symm_apply, id] at this
    simp only [e1, e2] at this
    rw [show ((m + 1 : ℕ) : ℝ) * δ = δ + m * δ by push_cast; ring]
    exact this

/-! ### Soundness of the `|x|`-fold protocol -/

/-- The sampler's coins fit in a block of the `|x|`-fold verifier's tape. -/
theorem permCoinLen_le_block {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 :=
  permCoinLen_le_tape G₀ G₁

/-- The guess of a prover with fixed coins `r₁` in iteration `i`, as a function of the graphs
`H_0, …, H_i` received: the first bit of its reply (the `g_i` of `uprob_gni_rep_cheat`). -/
noncomputable def gGuess {n : ℕ} (P' : Strategy) (x y : List Bool) (r₁ : P'.Coins x.length)
    (i : Fin x.length) (Ks : Fin (i + 1) → Graph n) (_ : Unit) : Bool :=
  (P'.next x y (List.ofFn r₁) (List.ofFn fun k => encGraph (Ks k))).headD false

/-- **The acceptance bound of the `|x|`-fold graph non-isomorphism protocol against isomorphic
graphs** [PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the
verifier accepts with probability at most `2^{-|x|} + |x| · permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); its `i`-th reply
is then a function `g_i` of the graphs `H_0, …, H_i` (`gGuess`). Read the verifier's tape as
the `|x|` pairs (bit, sampler coins) (`gniTapes`, `coinSlice_gniTapes`): the acceptance event is
`∀ i, g_i(σ_0(G_{b_0}), …, σ_i(G_{b_i})) = b_i` with `σ_j` sampled from block `j`. Replacing the
`|x|` sampled permutations by uniform ones costs `|x| · permFailBound n`
(`statClose_samplePerm_long`, `statClose_pi`, `StatClose.abs_uprob_sub_le_prod`), and for uniform
permutations the event has probability exactly `2^{-|x|}` (`uprob_gni_rep_cheat`). -/
theorem gniRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤
      (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length + (encInstance G₀ G₁).length * permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocolRep.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  -- the event on the verifier's tape, through the blocks
  have hev : ∀ p : (Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)),
      gniProtocolRep.outV P' (encInstance G₀ G₁) y z (r₁, gniTapes (encInstance G₀ G₁).length p) = [true] ↔
        ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i (prefixLE (fun j => permGraph (cond (p.1 j) G₁ G₀)
          (samplePerm n (List.ofFn (p.2 j)))) i) () = p.1 i := by
    rintro ⟨b, ts⟩
    rw [gniRep_outV_eq]
    simp only [List.cons.injEq, decide_eq_true_eq, and_true]
    refine forall_congr' fun i => ?_
    rw [coinSlice_gniTapes _ b ts i.isLt, List.headD_cons, gGuess,
      ofFn_eq_map_range (fun k : Fin (i + 1) => encGraph (prefixLE (fun j => permGraph (cond (b j) G₁ G₀)
        (samplePerm n (List.ofFn (ts j)))) i k)) (gniGraphs G₀ G₁ (List.ofFn (gniTapes _ (b, ts))))
        (fun t => by
          rw [gniGraphs, coinSlice_gniTapes _ b ts (by omega : (t : ℕ) < (encInstance G₀ G₁).length),
            List.headD_cons, List.drop_one, List.tail_cons]
          rfl)]
  rw [← uprob_comp_equiv (gniTapes (encInstance G₀ G₁).length), OneWay.uprob_congr hev,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (encInstance G₀ G₁).length →
      (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool)) (Fin (encInstance G₀ G₁).length → Bool))]
  have hclose := (statClose_pi (statClose_samplePerm_long (permCoinLen_le_block G₀ G₁))
    (encInstance G₀ G₁).length).abs_uprob_sub_le_prod
    fun (σs : Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n))
      (b : Fin (encInstance G₀ G₁).length → Bool) => ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (b j) G₁ G₀) (σs j)) i) () = b i
  have hideal : uprob (fun q : (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)) ×
      (Fin (encInstance G₀ G₁).length → Bool) =>
      ∀ i, gGuess P' (encInstance G₀ G₁) y r₁ i
        (prefixLE (fun j => permGraph (cond (q.2 j) G₁ G₀) (id q.1 j)) i) () = q.2 i) =
        (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
    rw [← uprob_comp_equiv ((Equiv.prodPUnit ((Fin (encInstance G₀ G₁).length → Bool) ×
      (Fin (encInstance G₀ G₁).length → Equiv.Perm (Fin n)))).trans (Equiv.prodComm _ _))]
    exact uprob_gni_rep_cheat hσ (gGuess P' (encInstance G₀ G₁) y r₁)
  rw [hideal] at hclose
  have h2 := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap] at h2 ⊢
  linarith

/-- **The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso` with
soundness error `2^{-|x|} + |x| · permFailBound n`** [PS10, Proposition 118.4] (Prop-118.4),
given the verifier's efficiency.

**Proof sketch.** Completeness is `gniRep_complete` with the empty auxiliary input. Soundness:
a well-formed `x ∉ L_niso` is `encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gniRep_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gniRep_outV_eq`, `uprob_not`); a malformed `x` is rejected on every
tape (`gniVerifierRep_next_ge`, `exec_vfirst_length`). -/
theorem gni_interactiveProofErrRep (hV : gniVerifierRep.Efficient) :
    InteractiveProofErr gniProtocolRep Lniso
      (fun N => (2 : ℝ)⁻¹ ^ N + N * permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], fun z => gniRep_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gniRep_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gniRep_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocolRep.ExecCoins P' x, gniProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocolRep_outV, gniVerifierRep_next_ge _ _ _ _
          (exec_vfirst_length P' gniVerifierRep x [] z (List.ofFn r.1) (List.ofFn r.2) x.length).2.ge]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have h1 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      have h2 : (0 : ℝ) ≤ x.length * permFailBound (instanceVertices x.length) :=
        mul_nonneg (Nat.cast_nonneg _) (permFailBound_nonneg _)
      linarith

/-- **[PS10, Proposition 118.4]:** the `|x|`-fold graph non-isomorphism protocol is an
interactive proof for `L_niso`, given the verifier's efficiency: the soundness error
`2^{-N} + N · permFailBound (instanceVertices N)` of `gni_interactiveProofErrRep` is
negligible (`negligible_two_pow_neg`, `negligible_mul_permFailBound`). -/
theorem gni_interactiveProof (hV : gniVerifierRep.Efficient) : InteractiveProof gniProtocolRep Lniso :=
  (gni_interactiveProofErrRep hV).interactiveProof (negligible_two_pow_neg.add negligible_mul_permFailBound)

end TCSlib.Cryptography.GI
