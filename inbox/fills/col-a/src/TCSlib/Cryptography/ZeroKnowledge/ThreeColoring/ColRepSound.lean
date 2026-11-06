/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphismZK.Closeness
import TCSlib.Cryptography.Asymptotic.OneWayLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: generic lemmas for the repeated protocol

Generic infrastructure for `colRep_efficientProverProof` (`ThreeColoring/Protocol.lean`), the
interactive-proof half of [PS10, Proposition 127.6] for the `n|E|`-fold protocol (Prot-127.5,
repeated). Nothing here names the protocol's parties.

* **Four-move iterations against a challenge verifier** (`exec_four_mul`): in a prover-first
  execution whose verifier answers every odd history of `2i + 1` messages with the challenge
  `ch i` and every shorter even history (fewer than `2N` messages) with `[]`, after `4i ≤ 4N`
  moves the verifier has received the prover's commitments `P'(chView ch j)` and replies
  `P'(chView ch j ++ [ch j])` (`j < i`) interleaved, and before the last iteration the prover
  has received `chView ch i = [ch 0, [], …, ch (i-1), []]`.
* **Blocks of a tape** (`blockRead`): reading the first `K` blocks of `b` bits of a tape of
  `C ≥ K b` bits pushes the uniform tape to `K` independent uniform blocks
  (`pushesUniform_blockRead`); the list form of a block is the list slice
  (`drop_take_ofFn_blockRead`).
* **`K` edge samplers** (`statClose_edgeBlocks`): the rejection-sampled edge indices of `K`
  blocks are `K (1/2)^T`-close to `K` independent uniform indices
  (`statClose_sampleEdgeIdx` per block, `OneWay.statClose_pi`).
* **The number of iterations** (`mul_edgeCount_le`): `n |E| ≤ |x|²` on an encoded graph.

## Main definitions

* `TCSlib.Cryptography.ColRep.chView` — the prover's view `[ch 0, [], …, ch (i-1), []]`.
* `TCSlib.Cryptography.ColRep.blockRead` — the first `K` blocks of `b` bits of a tape.

## Main results

* `TCSlib.Cryptography.ColRep.exec_four_mul` — the views of `4i` moves against a challenge
  verifier.
* `TCSlib.Cryptography.ColRep.pushesUniform_blockRead`,
  `TCSlib.Cryptography.ColRep.drop_take_ofFn_blockRead` — tape blocks.
* `TCSlib.Cryptography.ColRep.statClose_edgeBlocks` — `K` edge samplers are close to uniform.
* `TCSlib.Cryptography.ColRep.mul_edgeCount_le` — `n |E| ≤ |x|²` on an encoded graph.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.ColRep

open Complexity Turing

/-! ### The prover's view against a challenge verifier -/

/-- The prover's view after `i` iterations against a verifier that sends the challenge `ch j`
and then the empty message in iteration `j`: `[ch 0, [], ch 1, [], …, ch (i-1), []]`. -/
def chView (ch : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => chView ch i ++ [ch i, []]

/-- `chView ch 0 = []`. -/
theorem chView_zero (ch : ℕ → List Bool) : chView ch 0 = [] := rfl

/-- `chView ch (i + 1) = chView ch i ++ [ch i, []]`. -/
theorem chView_succ (ch : ℕ → List Bool) (i : ℕ) : chView ch (i + 1) = chView ch i ++ [ch i, []] :=
  rfl

/-- The prover's view after `i` iterations has `2i` messages. -/
theorem length_chView (ch : ℕ → List Bool) : ∀ i, (chView ch i).length = 2 * i
  | 0 => rfl
  | i + 1 => by
    rw [chView_succ, List.length_append, length_chView ch i]
    rfl

/-- The prover's view after `i` iterations depends only on the first `i` challenges. -/
theorem chView_congr {f g : ℕ → List Bool} : ∀ i, (∀ k < i, f k = g k) → chView f i = chView g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [chView_succ, chView_succ, chView_congr i (fun k hk => h k (by omega)), h i (by omega)]

/-- **Four-move iterations against a challenge verifier** [PS10, Protocol 127.5, repeated]: in
the prover-first execution `P'_{rP}(x, y) ↔ V_{rV}(x, z)`, if `V` answers every odd history of
`2j + 1` messages with `ch j` and every even history of fewer than `2N` messages with `[]`,
then for `i ≤ N` after `4i` moves the verifier has received `2i` messages, message `2j` being
`P'(chView ch j)` and message `2j + 1` being `P'(chView ch j ++ [ch j])` for `j < i`, and, if
`i < N`, the prover has received `chView ch i`.

**Proof sketch.** Induction on `i`: four applications of `exec_succ` (`moverIsV_false`: the
prover moves at `4i`, `4i + 2`); the challenge is `ch i` (`hodd` on `2i + 1` messages) and the
fourth message is `[]` while `2i + 2 < 2N` (`hmid`); the new messages are appended at the end
(`List.getD_append`, `List.getD_append_right`). -/
theorem exec_four_mul (P' V : Strategy) (x y z rP rV : List Bool) (ch : ℕ → List Bool) (N : ℕ)
    (hodd : ∀ hist : List (List Bool), hist.length % 2 = 1 →
      V.next x z rV hist = ch (hist.length / 2))
    (hmid : ∀ hist : List (List Bool), hist.length % 2 = 0 → hist.length < 2 * N →
      V.next x z rV hist = []) :
    ∀ i, i ≤ N → (exec P' V false x y z rP rV (4 * i)).2.length = 2 * i ∧
      (∀ j < i, (exec P' V false x y z rP rV (4 * i)).2.getD (2 * j) [] =
          P'.next x y rP (chView ch j) ∧
        (exec P' V false x y z rP rV (4 * i)).2.getD (2 * j + 1) [] =
          P'.next x y rP (chView ch j ++ [ch j])) ∧
      (i < N → (exec P' V false x y z rP rV (4 * i)).1 = chView ch i)
  | 0, _ => by
    rw [Nat.mul_zero, exec_zero]
    exact ⟨rfl, fun j hj => absurd hj (Nat.not_lt_zero _), fun _ => (chView_zero ch).symm⟩
  | i + 1, hi => by
    obtain ⟨hlen, hget, hP⟩ := exec_four_mul P' V x y z rP rV ch N hodd hmid i (by omega)
    have hPi := hP (by omega)
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
    set E := exec P' V false x y z rP rV (4 * i) with hE
    have hstep : exec P' V false x y z rP rV (4 * (i + 1)) =
        (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1]),
            V.next x z rV (E.2 ++ [P'.next x y rP E.1,
              P'.next x y rP (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1])])])],
          E.2 ++ [P'.next x y rP E.1,
            P'.next x y rP (E.1 ++ [V.next x z rV (E.2 ++ [P'.next x y rP E.1])])]) := by
      rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by ring, exec_succ, exec_succ, exec_succ,
        exec_succ, ← hE]
      simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, List.append_assoc,
        List.singleton_append]
    have hb : V.next x z rV (E.2 ++ [P'.next x y rP E.1]) = ch i := by
      rw [hodd _ (by rw [List.length_append, hlen, List.length_singleton]; omega),
        List.length_append, hlen, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    rw [hstep, hb, hPi]
    refine ⟨?_, fun j hj => ?_, fun hN => ?_⟩
    · rw [List.length_append, hlen]
      rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj' | rfl
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact hget j hj'
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega),
          hlen, Nat.sub_self, show 2 * j + 1 - 2 * j = 1 by omega]
        exact ⟨rfl, rfl⟩
    · rw [hmid _ (by rw [List.length_append, hlen, List.length_cons, List.length_singleton]; omega)
        (by rw [List.length_append, hlen, List.length_cons, List.length_singleton]; omega),
        chView_succ]

/-! ### Blocks of a tape -/

/-- The first `K` blocks of `b` bits of a tape of `C ≥ K b` bits: bit `j` of block `t` is bit
`t b + j` of the tape. -/
def blockRead (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) (j : Fin b) : Bool :=
  r ⟨t * b + j, by
    calc (t : ℕ) * b + j < (t : ℕ) * b + b := by omega
      _ = ((t : ℕ) + 1) * b := by ring
      _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
      _ ≤ C := h⟩

/-- The defining equation of `blockRead`: bit `j` of block `t` is bit `t b + j` of the tape. -/
theorem blockRead_eq (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) (j : Fin b) :
    blockRead b K C h r t j = r ⟨t * b + j, by
      calc (t : ℕ) * b + j < (t : ℕ) * b + b := by omega
        _ = ((t : ℕ) + 1) * b := by ring
        _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
        _ ≤ C := h⟩ := rfl

/-- **The blocks of a uniform tape are independent and uniform**: `blockRead` is the restriction
to the first `K b` bits (`GIZK.pushesUniform_castLE`) followed by the bijection
`(Fin (K b) → Bool) ≃ (Fin K → Fin b → Bool)` (`finProdFinEquiv`, `Equiv.curry`). -/
theorem pushesUniform_blockRead (b K C : ℕ) (h : K * b ≤ C) :
    HardcoreBit.PushesUniform (blockRead b K C h) := by
  let e : (Fin (K * b) → Bool) ≃ (Fin K → Fin b → Bool) :=
    (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)
  have he : ∀ s : Fin (K * b) → Bool, ∀ t j, e s t j = s (finProdFinEquiv (t, j)) := by
    intro s t j
    rfl
  have hc := (GIZK.pushesUniform_castLE (B := Bool) h).comp (HardcoreBit.pushesUniform_equiv e)
  convert hc using 1
  funext r t j
  rw [he, blockRead_eq]
  congr 1
  apply Fin.ext
  simp only [Fin.coe_castLE, finProdFinEquiv_apply_val]
  ring

/-- The list slice of block `t` of a tape is the list of the block:
`((List.ofFn r).drop (t b)).take b = List.ofFn (blockRead b K C h r t)`. -/
theorem drop_take_ofFn_blockRead (b K C : ℕ) (h : K * b ≤ C) (r : Fin C → Bool) (t : Fin K) :
    ((List.ofFn r).drop (t * b)).take b = List.ofFn (blockRead b K C h r t) := by
  have hle : (t : ℕ) * b + b ≤ C := by
    calc (t : ℕ) * b + b = ((t : ℕ) + 1) * b := by ring
      _ ≤ K * b := Nat.mul_le_mul_right b t.isLt
      _ ≤ C := h
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro k h1 h2
    rw [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_ofFn, blockRead_eq]

/-! ### Independent edge samplers -/

/-- **`K` rejection-sampled edge indices are close to uniform** [PS10, Protocol 127.5 with the
sampler of D10]: on a uniform tape of `C ≥ K b` bits, the edge indices `sampleEdgeIdx m T` of
the first `K` blocks of `b ≥ T ⌈log m⌉` bits are `K (1/2)^T`-close to `K` independent uniform
indices in `[m]`.

**Proof sketch.** One block: `statClose_sampleEdgeIdx` on the first `T · size m` bits of the
block (`GIZK.pushesUniform_castLE`, `ColProofs.sampleEdgeIdx_ofFn_castLE`); `K` blocks:
`OneWay.statClose_pi`; the tape: `pushesUniform_blockRead` (`StatClose.comp_pushesUniform`). -/
theorem statClose_edgeBlocks {m : ℕ} (hm : 0 < m) (T b K C : ℕ) (hb : T * Nat.size m ≤ b)
    (h : K * b ≤ C) :
    StatClose (fun r : Fin C → Bool => fun t : Fin K =>
        (⟨sampleEdgeIdx m T (List.ofFn (blockRead b K C h r t)), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : (Fin K → Fin m) → Fin K → Fin m) (K * (1 / 2 : ℝ) ^ T) := by
  have h1 : StatClose (fun g : Fin b → Bool =>
      (⟨sampleEdgeIdx m T (List.ofFn g), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : Fin m → Fin m) ((1 / 2 : ℝ) ^ T) := by
    have h0 := (statClose_sampleEdgeIdx hm T).comp_pushesUniform
      (GIZK.pushesUniform_castLE (B := Bool) hb)
    convert h0 using 2 with g
    exact Fin.ext (ColProofs.sampleEdgeIdx_ofFn_castLE hb g)
  exact (OneWay.statClose_pi h1 K).comp_pushesUniform (pushesUniform_blockRead b K C h)

/-! ### The number of iterations -/

/-- On an encoded graph `n |E| ≤ |x|²`: `|E| ≤ n²` (`ColMachines.edgeCount_eq`,
`ColMachines.countTrue_le`) and `n · n² ≤ n⁴` (the `n|E|` iterations of the repeated protocol fit in
its `|x|²` slots, [PS10, Protocol 127.5]). -/
theorem mul_edgeCount_le {n : ℕ} (G : Graph n) :
    n * edgeCount G ≤ (encGraph G).length * (encGraph G).length := by
  have hm : edgeCount G ≤ n * n := by
    rw [ColMachines.edgeCount_eq G (encGraph G) fun u v => (encGraph_getD G u v).symm]
    exact ColMachines.countTrue_le _ _
  rw [length_encGraph]
  calc n * edgeCount G ≤ n * (n * n) := Nat.mul_le_mul_left n hm
    _ ≤ n * n * (n * n) := Nat.mul_le_mul_right (n * n) (Nat.le_mul_self n)

end TCSlib.Cryptography.ColRep
