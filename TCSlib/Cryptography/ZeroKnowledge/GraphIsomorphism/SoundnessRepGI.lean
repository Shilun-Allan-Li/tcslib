/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph isomorphism protocol: completeness and soundness

[PS10, Proposition 120.7] for the `|x|`-fold protocol `giProtocolRep` (Prot-120.6, repeated,
four moves per iteration), proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`;
the main file closes `gi_rep_efficientProverProof` by
`exact GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient`.

The execution is described iteration by iteration (`repViews`, `exec_repViews`): in iteration
`i` the prover sends `H_i`, the verifier the challenge `[b_i]` with `b_i` its `i`-th coin
(`giVerifierRep_next_odd`), the prover `γ_i`, and the verifier the empty message (or, in the
last iteration, its verdict). The verifier's view is the interleaving `Vs` of the `H_i` and
`γ_i`; the prover's view, before the last iteration, is determined by the challenges
(`PsOf`). **Completeness** is exact (`gi_honest_reply_eq`). **Soundness**: the accepting event
implies the typed event of `uprob_gi_rep_cheat_le` (Lem-120.d) with `H_i` a function of the
earlier challenges and `γ_i` of the challenges up to `i`, whence `Pr[accept] ≤ 2^{-|x|}`.

## Main definitions

* `TCSlib.Cryptography.GI.repViews` — the two parties' views after `i` iterations.
* `TCSlib.Cryptography.GI.Vs`, `GI.PsOf`, `GI.PsOfFin` — the verifier's and the prover's views
  as functions of the messages and challenges.

## Main results

* `TCSlib.Cryptography.GI.exec_repViews` — the four-move iterations of a prover-first protocol.
* `TCSlib.Cryptography.GI.giRep_complete`, `GI.giRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr`, `GI.gi_rep_efficientProverProof` —
  [PS10, Proposition 120.7] for the repeated protocol.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Four-move iterations of a prover-first protocol -/

/-- The views (prover's received messages, verifier's received messages) after `i` iterations
of four moves: the prover sends `H`, the verifier `b`, the prover `γ`, the verifier `e`. -/
def repViews (P' V : Strategy) (x y z rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | i + 1 =>
    let v := repViews P' V x y z rP rV i
    let H := P'.next x y rP v.1
    let b := V.next x z rV (v.2 ++ [H])
    let γ := P'.next x y rP (v.1 ++ [b])
    let e := V.next x z rV (v.2 ++ [H, γ])
    (v.1 ++ [b, e], v.2 ++ [H, γ])

/-- After `4i` moves of a prover-first execution the views are `repViews i`
(`moverIsV false k = decide (k % 2 = 1)`: the prover moves at `4i` and `4i + 2`, the verifier
at `4i + 1` and `4i + 3`). -/
theorem exec_repViews (P' V : Strategy) (x y z rP rV : List Bool) :
    ∀ i, exec P' V false x y z rP rV (4 * i) = repViews P' V x y z rP rV i
  | 0 => rfl
  | i + 1 => by
    have h0 : moverIsV false (4 * i) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h1 : moverIsV false (4 * i + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    have h2 : moverIsV false (4 * i + 1 + 1) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h3 : moverIsV false (4 * i + 1 + 1 + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by ring, exec_succ, exec_succ, exec_succ, exec_succ,
      exec_repViews P' V x y z rP rV i]
    simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, repViews, List.append_assoc,
      List.singleton_append]

/-- The verifier's view after `i` iterations as the interleaving of the graphs and replies. -/
def Vs (H γ : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => Vs H γ i ++ [H i, γ i]

/-- The verifier's view after `i` iterations has `2i` messages. -/
theorem length_Vs (H γ : ℕ → List Bool) : ∀ i, (Vs H γ i).length = 2 * i
  | 0 => rfl
  | i + 1 => by
    rw [Vs, List.length_append, length_Vs H γ i]
    rfl

/-- Message `2j` of the verifier's view is the graph `H_j`. -/
theorem getD_Vs_even (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j) [] = H j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_even H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]), length_Vs, Nat.sub_self]
      rfl

/-- Message `2j + 1` of the verifier's view is the reply `γ_j`. -/
theorem getD_Vs_odd (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j + 1) [] = γ j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_odd H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]; omega), length_Vs,
        show 2 * j + 1 - 2 * j = 1 by omega]
      rfl

/-- The prover's view after `i` iterations when the verifier's even messages are empty: the
challenges `[b_0], [], …, [b_{i-1}], []`. -/
def PsOf (b : ℕ → Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => PsOf b i ++ [[b i], []]

/-- The prover's view depends only on the first `i` challenges. -/
theorem PsOf_congr {f g : ℕ → Bool} : ∀ i, (∀ k < i, f k = g k) → PsOf f i = PsOf g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [PsOf, PsOf, PsOf_congr i (fun k hk => h k (by omega)), h i (by omega)]

/-- The prover's view as a function of a tuple of challenges. -/
def PsOfFin {i : ℕ} (bs : Fin i → Bool) : List (List Bool) :=
  PsOf (fun k => if h : k < i then bs ⟨k, h⟩ else false) i

/-- The prover's view from the strict prefix of a challenge tuple is its view from the tape. -/
theorem PsOfFin_prefixLT {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (prefixLT b i) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The prover's view from the initial segment of a challenge prefix is its view from the tape. -/
theorem PsOfFin_init_prefixLE {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (Fin.init (prefixLE b i)) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The last challenge of a prefix `b_0, …, b_i` is `b_i`. -/
theorem prefixLE_last {m : ℕ} (b : Fin m → Bool) (i : Fin m) : prefixLE b i (Fin.last i) = b i := rfl

/-! ### The `|x|`-fold graph isomorphism verifier and prover, unfolded -/

/-- The `|x|`-fold verifier's challenge on an odd history: its coin `|hist| / 2`. -/
theorem giVerifierRep_next_odd (x z r : List Bool) (hist : List (List Bool)) (h : hist.length % 2 = 1) :
    giVerifierRep.next x z r hist = [r.getD (hist.length / 2) false] := by
  show (if hist.length % 2 = 1 then _ else _) = _
  rw [if_pos h]

/-- The `|x|`-fold verifier's empty message on an even history of fewer than `2|x|` messages. -/
theorem giVerifierRep_next_mid (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : hist.length < 2 * x.length) : giVerifierRep.next x z r hist = [] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_pos h2]

/-- The `|x|`-fold verifier's verdict on an even complete history. -/
theorem giVerifierRep_next_end (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : ¬ hist.length < 2 * x.length) :
    giVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
          (decPerm (instanceVertexCount x) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_neg h2]

/-- The `|x|`-fold verifier's verdict on an encoded instance: `γ_j(G_{b_j}) = H_j` for every
iteration, with the graphs read on `n` vertices. -/
theorem giVerifierRep_next_end_enc {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h1 : hist.length % 2 ≠ 1) (h2 : ¬ hist.length < 2 * (encInstance G₀ G₁).length) :
    giVerifierRep.next (encInstance G₀ G₁) z r hist =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        encGraph (permGraph (cond (r.getD j false) G₁ G₀) (decPerm n (hist.getD (2 * j + 1) []))) =
          hist.getD (2 * j) [])] := by
  rw [giVerifierRep_next_end _ _ _ _ h1 h2, wellFormedInstance_encInstance]
  simp only [true_and]
  show [decide (∀ j : Fin (encInstance G₀ G₁).length, encGraph (permGraph
    (if r.getD j false then decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁))
      else decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decPerm (instanceVertexCount (encInstance G₀ G₁)) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph, Bool.cond_eq_ite]

/-- The `|x|`-fold prover's graph on an even history of an encoded instance: `π(G₀)` for the
permutation sampled from coin block `|hist| / 2`. -/
theorem giProverRep_next_even {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool))
    (h : hist.length % 2 = 0) :
    giProverRep.next (encInstance G₀ G₁) y r hist =
      encGraph (permGraph G₀ (samplePerm n
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) := by
  show (if hist.length % 2 = 0 then encGraph (permGraph
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) else _) = _
  rw [if_pos h, show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold prover's reply on an odd history of an encoded instance with witness
`encPerm σ`: `π σ⁻¹` or `π` according to the last challenge received. -/
theorem giProverRep_next_odd {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r : List Bool)
    (hist : List (List Bool)) (h : hist.length % 2 ≠ 0) :
    giProverRep.next (encInstance G₀ G₁) (encPerm σ) r hist =
      encPerm (if (hist.getLastD []).headD false then
        samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) * σ⁻¹
      else samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r)) := by
  show (if hist.length % 2 = 0 then _ else encPerm (if (hist.getLastD []).headD false then
    samplePerm (instanceVertexCount (encInstance G₀ G₁))
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) *
      (decPerm (instanceVertexCount (encInstance G₀ G₁)) (encPerm σ))⁻¹
    else samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) = _
  rw [if_neg h]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decPerm_encPerm]

/-- The verdict of the `|x|`-fold protocol against `P'`: the verifier's next-message function on
the `4|x|`-move execution. -/
theorem giProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : giProtocolRep.ExecCoins P' x) :
    giProtocolRep.outV P' x y z r =
      giVerifierRep.next x z (List.ofFn r.2)
        (exec P' giVerifierRep false x y z (List.ofFn r.1) (List.ofFn r.2) (4 * x.length)).2 := rfl

/-! ### The views against the honest verifier -/

/-- Against the `|x|`-fold verifier, the verifier's view after `i` iterations interleaves the
prover's graphs (its next message on its view) and replies (its next message on its view
extended by the challenge `[b_j]`, `b_j` the verifier's `j`-th coin), and the prover's view
has `2i` messages.

**Proof sketch.** Induction on `i`: the challenge is the verifier's coin `i`
(`giVerifierRep_next_odd` on the odd history of `2i + 1` messages). -/
theorem repViews_snd (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, (repViews P' giVerifierRep x y z rP rV i).2 =
      Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
        (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ∧
      (repViews P' giVerifierRep x y z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    simp only [repViews]
    rw [h2, hb]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- Against the `|x|`-fold verifier, before the last iteration the prover's view is determined
by the challenges.

**Proof sketch.** Induction on `i < |x|`: the challenge of iteration `i` is the verifier's coin
`i` (`giVerifierRep_next_odd`) and its fourth message is empty, the history having `2i + 2 < 2|x|`
messages (`giVerifierRep_next_mid`). -/
theorem repViews_fst (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, i < x.length → (repViews P' giVerifierRep x y z rP rV i).1 = PsOf (fun k => rV.getD k false) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := repViews_fst P' x y z rP rV i (by omega)
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have he : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1,
            P'.next x y rP ((repViews P' giVerifierRep x y z rP rV i).1 ++ [[rV.getD i false]])]) = [] := by
      apply giVerifierRep_next_mid
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
    simp only [repViews]
    rw [h2, hb, he, ih]
    rfl

/-! ### Completeness -/

/-- The honest prover's graph of iteration `j`: `π_j(G₀)` for `π_j` sampled from coin block `j`
(block length `c`) of its tape. -/
noncomputable def honestH {n : ℕ} (G₀ : Graph n) (c : ℕ) (rP : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph G₀ (samplePerm n (coinSlice c j rP)))

/-- The honest prover's reply of iteration `j`: `π_j σ⁻¹` or `π_j` according to the verifier's
coin `j`. -/
noncomputable def honestγ {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : ℕ) (rP rV : List Bool) (j : ℕ) : List Bool :=
  encPerm (if rV.getD j false then samplePerm n (coinSlice c j rP) * σ⁻¹ else samplePerm n (coinSlice c j rP))

/-- The honest views on an encoded instance with witness `encPerm σ`: the verifier's view
interleaves `honestH` and `honestγ`.

**Proof sketch.** Induction on `i` with `giProverRep_next_even` (the prover's view has `2i`
messages), `giVerifierRep_next_odd` (the verifier's has `2i + 1`) and `giProverRep_next_odd`
(the last message the prover received is the challenge `[b_i]`, `List.getLastD_concat`). -/
theorem honest_views {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z rP rV : List Bool) :
    ∀ i, (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).2 =
        Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ∧
      (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := honest_views G₀ G₁ σ z rP rV i
    have hH : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 =
        encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP))) := by
      rw [giProverRep_next_even _ _ _ _ _ (by rw [h1]; omega), h1, show 2 * i / 2 = i by omega]
    have hb : giVerifierRep.next (encInstance G₀ G₁) z rV
        (Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ++
          [encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP)))]) =
        [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have hγ : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        ((repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 ++ [[rV.getD i false]]) =
        honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV i := by
      rw [giProverRep_next_odd _ _ _ _ _ (by rw [List.length_append, h1, List.length_singleton]; omega),
        List.getLastD_concat, List.headD_cons, List.length_append, h1, List.length_singleton,
        show (2 * i + 1) / 2 = i by omega]
      rfl
    simp only [repViews]
    rw [h2, hH, hb, hγ]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- **Completeness of the `|x|`-fold graph isomorphism protocol for every witness**
[PS10, Proposition 120.7]: every iteration's check `γ_j(G_{b_j}) = H_j` holds on the honest
views (`honest_views`, `gi_honest_reply_eq`), for every pair of tapes. -/
theorem giRep_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins giProverRep (encInstance G₀ G₁) =>
      giProtocolRep.outV giProverRep (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [giProtocolRep_outV, exec_repViews, (honest_views G₀ G₁ σ z _ _ _).1,
    giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  intro j
  rw [getD_Vs_odd _ _ _ _ j.isLt, getD_Vs_even _ _ _ _ j.isLt, honestγ, honestH, decPerm_encPerm,
    gi_honest_reply_eq hσ]

/-! ### Soundness -/

/-- The joint coins of the `|x|`-fold graph isomorphism protocol as (challenges, prover's
coins). -/
def giRepCoins (P' : Strategy) (x : List Bool) :
    (Fin x.length → Bool) × P'.Coins x.length ≃ giProtocolRep.ExecCoins P' x :=
  Equiv.prodComm _ _

/-- The decoded graph a prover with coins `r₁` sends in iteration `i` after the challenges `bs`
(the `H_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def Hfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length) (bs : Fin i → Bool)
    (r₁ : P'.Coins x.length) : Graph n :=
  decGraphAt n (P'.next x y (List.ofFn r₁) (PsOfFin bs))

/-- The decoded permutation a prover with coins `r₁` replies in iteration `i` after the
challenges `bs` (the last one being the current challenge; the `γ_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def γfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length)
    (bs : Fin (i + 1) → Bool) (r₁ : P'.Coins x.length) : Equiv.Perm (Fin n) :=
  decPerm n (P'.next x y (List.ofFn r₁) (PsOfFin (Fin.init bs) ++ [[bs (Fin.last i)]]))

/-- **The acceptance bound of the `|x|`-fold graph isomorphism protocol against non-isomorphic
graphs** [PS10, Proposition 120.7, "repeated … to drive the error as low as desired"]: for
`G₀ ≇ G₁` and every prover `P'`, the verifier accepts with probability at most `2^{-|x|}`.

**Proof sketch.** Acceptance means `γ_j(G_{b_j}) = H_j` for every `j` (`giVerifierRep_next_end_enc`,
`repViews_snd`), where `H_j` is the prover's message on its view `PsOf b j` and `γ_j` on
`PsOf b j ++ [[b_j]]` (`repViews_fst`); decoding both sides (`decGraphAt_encGraph`) gives the
event of `uprob_gi_rep_cheat_le` with `Hfun`, `γfun` (`PsOfFin_prefixLT`, `PsOfFin_init_prefixLE`),
after reading the joint coins as (challenges, prover's coins) (`giRepCoins`). -/
theorem giRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
  have hmono : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true] →
      ∀ i : Fin (encInstance G₀ G₁).length,
        permGraph (cond ((List.ofFn r.2).getD i false) G₁ G₀)
          (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
            (PsOf (fun k => (List.ofFn r.2).getD k false) i ++ [[(List.ofFn r.2).getD i false]]))) =
        decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (PsOf (fun k => (List.ofFn r.2).getD k false) i)) := by
    intro r hr i
    rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ y z _ _ _).1,
      giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    have hi := hr i
    rw [getD_Vs_odd _ _ _ _ i.isLt, getD_Vs_even _ _ _ _ i.isLt, repViews_fst P' _ y z _ _ i i.isLt] at hi
    rw [← hi, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giRepCoins P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_)
    (uprob_gi_rep_cheat_le h (Hfun P' (encInstance G₀ G₁) y) (γfun P' (encInstance G₀ G₁) y))
  rintro ⟨b, r₁⟩
  refine forall_congr' fun i => ?_
  show permGraph (cond ((List.ofFn b).getD i false) G₁ G₀) (decPerm n (P'.next _ y (List.ofFn r₁)
      (PsOf (fun k => (List.ofFn b).getD k false) i ++ [[(List.ofFn b).getD i false]]))) =
    decGraphAt n (P'.next _ y (List.ofFn r₁) (PsOf (fun k => (List.ofFn b).getD k false) i)) ↔
    permGraph (cond (b i) G₁ G₀) (γfun P' _ y i (prefixLE b i) r₁) = Hfun P' _ y i (prefixLT b i) r₁
  rw [getD_ofFn_lt' b i.isLt, Hfun, γfun, PsOfFin_init_prefixLE, prefixLE_last, PsOfFin_prefixLT]

/-- **The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
soundness error `2^{-|x|}` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, repeated] (Prop-120.7, Lem-120.d), given the parties' efficiency.

**Proof sketch.** Completeness for every witness is `giRep_complete`; soundness is
`giRep_accept_le` on well-formed inputs (a well-formed `x ∉ L_iso` has non-isomorphic graphs)
and the outright rejection of malformed inputs (`giVerifierRep_next_end`). -/
theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProofErr giProtocolRep Liso Riso (fun N => (2 : ℝ)⁻¹ ^ N) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, fun z => giRep_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := giRep_accept_le hni P' [] z
      have hnot : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ [] z _ _ _).1,
          giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocolRep.ExecCoins P' x, giProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, giVerifierRep_next_end _ _ _ _
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      linarith
  efficientP := hP
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact giRep_complete hσ z

/-- **[PS10, Proposition 120.7], repeated:** the `|x|`-fold graph isomorphism protocol is an
interactive proof for `L_iso` with efficient prover with respect to `R_iso`, given the
parties' efficiency (`gi_rep_efficientProverProofErr`, `negligible_two_pow_neg`). -/
theorem gi_rep_efficientProverProof (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProof giProtocolRep Liso Riso :=
  (gi_rep_efficientProverProofErr hP hV).efficientProverProof negligible_two_pow_neg

end TCSlib.Cryptography.GI
