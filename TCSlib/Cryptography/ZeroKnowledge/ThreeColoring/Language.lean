/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.Asymptotic.Adversary
import Mathlib.Combinatorics.SimpleGraph.Coloring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Graph 3-colouring: the language, its witnesses, edges, colours and samplers

The combinatorial and sampling preliminaries of the zero-knowledge protocol for graph
3-colouring [PS10, §4.7]: the language of 3-colourable graphs and its witness relation
[PS10, Theorem 124.1, step 1] (Def-124.f), the enumeration of the edges of a graph (the set
`E` of [PS10, Protocol 127.5]), the bound `(1 - 1/m)^{nm} ≤ e^{-n}` of the soundness analysis
(Claim-125.a), colours as `n`-bit committed values (DQ4), and the rejection samplers of the
honest parties for the colour permutation `π ← S₃` and the edge `e ← E` (D10).

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours
(`ThreeColorable` agrees with Mathlib's `SimpleGraph.Colorable 3` on simple graphs,
`threeColorable_ofSimpleGraph_iff`). The edges are listed in lexicographic order
(`edgeList`), the verifier's challenge is an index into that list, sent in unary
(`edgeMsg`) and decoded totally (`edgeIdxOfMsg`).

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation and `edgeList`
lists the *ordered* pairs `(u, v)` with `G u v` (loops included), so for the text's symmetric
loopless `G = (V, E)` the formal `|E| := edgeCount G` is `2|E|`: one iteration has soundness
error `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|` times; the challenge is
uniform over the ordered pairs, i.e. uniform over the undirected edges, and the bound
`(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. Throughout `ThreeColoring/`, `|E|` means `edgeCount G`.

**Deviation (DQ4, D10):** colours are padded to `n` bits (`padColor`; the text commits to
2-bit colours, i.e. at security parameter `2`); `π` and `e` are sampled by rejection from the
bit tapes (`samplePerm3`, `sampleEdgeIdx`) within statistical error `(1/4)^T`, `(1/2)^T`.

## Main definitions

* `TCSlib.Cryptography.ProperColoring`, `TCSlib.Cryptography.ThreeColorable`,
  `TCSlib.Cryptography.L3COL`, `TCSlib.Cryptography.R3COL` — 3-colourings, the language of
  3-colourable graphs and its witness relation (Def-124.f).
* `TCSlib.Cryptography.edgeList`, `TCSlib.Cryptography.edgeCount`,
  `TCSlib.Cryptography.edgeOf`, `TCSlib.Cryptography.edgeAt` — the edges and their indices.
* `TCSlib.Cryptography.encColor`, `TCSlib.Cryptography.decColor`,
  `TCSlib.Cryptography.padColor` — colours as 2-bit strings and as `n`-bit values.
* `TCSlib.Cryptography.sampleIdx`, `TCSlib.Cryptography.samplePerm3`,
  `TCSlib.Cryptography.sampleEdgeIdx`, `TCSlib.Cryptography.edgeMsg`,
  `TCSlib.Cryptography.edgeIdxOfMsg` — the samplers and the challenge encoding.

## Main results

* `TCSlib.Cryptography.mem_L3COL_iff`, `TCSlib.Cryptography.encGraph_mem_L3COL_iff`,
  `TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff` — the language and its witnesses.
* `TCSlib.Cryptography.mem_edgeList_iff`, `TCSlib.Cryptography.edgeAt_adj`,
  `TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero`,
  `TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable` — edges (all proved).
* `TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp`, `TCSlib.Cryptography.exp_neg_le_inv_two_pow`
  — `(1 - 1/m)^{nm} ≤ e^{-n} ≤ 2^{-n}` (Claim-125.a, proved).
* `TCSlib.Cryptography.padColor_injective` — padding to `n ≥ 2` bits is injective (proved).
* `TCSlib.Cryptography.statClose_samplePerm3`, `TCSlib.Cryptography.statClose_sampleEdgeIdx`
  — the samplers are statistically close to uniform (D10, proved).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### 3-colourings and the language `3COL` (Def-124.f) -/

/-- A proper 3-colouring of the graph `G` [PS10, §4.7, Theorem 124.1, step 1]: the endpoints
of every edge receive different colours (`c : Fin n → Fin 3`, colours `{1, 2, 3}` as `Fin 3`). -/
def ProperColoring {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Prop :=
  ∀ u v, G u v = true → c u ≠ c v

instance {n : ℕ} (G : Graph n) (c : Fin n → Fin 3) : Decidable (ProperColoring G c) := by
  unfold ProperColoring
  infer_instance

/-- A graph is 3-colourable when it has a proper 3-colouring [PS10, §4.7] (Def-124.f, typed). -/
def ThreeColorable {n : ℕ} (G : Graph n) : Prop := ∃ c, ProperColoring G c

/-- The graph of a Mathlib simple graph on `Fin n` as a Boolean relation. -/
def Graph.ofSimpleGraph {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] : Graph n :=
  fun u v => decide (H.Adj u v)

/-- Sanity: for a simple graph the notion agrees with Mathlib's `SimpleGraph.Colorable 3`
(a `Coloring` into `Fin 3` is exactly a proper 3-colouring). -/
theorem threeColorable_ofSimpleGraph_iff {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    ThreeColorable (Graph.ofSimpleGraph H) ↔ H.Colorable 3 := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {u v} h => hc u v (decide_eq_true h)⟩
  · rintro ⟨C⟩
    exact ⟨C, fun u v h => C.valid (of_decide_eq_true h)⟩

/-- The language of 3-colourable graphs [PS10, §4.7, "Graph 3-Coloring"] (Def-124.f): the
adjacency-matrix encodings of the 3-colourable graphs. -/
def L3COL : Language Bool := {x | ∃ (n : ℕ) (G : Graph n), x = encGraph G ∧ ThreeColorable G}

/-- The witness relation of `3COL` [PS10, §4.7] (Def-124.f): `y` is the encoding of a proper
3-colouring of the graph encoded by `x`. -/
def R3COL (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G : Graph n) (c : Fin n → Fin 3),
    x = encGraph G ∧ y = encColoring c ∧ ProperColoring G c

/-- `x ∈ 3COL` iff `x` has a witness for `R_3COL`. -/
theorem mem_L3COL_iff (x : List Bool) : x ∈ L3COL ↔ ∃ y, R3COL x y := by
  constructor
  · rintro ⟨n, G, rfl, c, hc⟩
    exact ⟨encColoring c, n, G, c, rfl, rfl, hc⟩
  · rintro ⟨y, n, G, c, rfl, -, hc⟩
    exact ⟨n, G, rfl, c, hc⟩

/-- An encoded graph is in `3COL` iff the graph is 3-colourable (`decGraph_encGraph`
identifies the graph from its encoding). -/
theorem encGraph_mem_L3COL_iff {n : ℕ} (G : Graph n) : encGraph G ∈ L3COL ↔ ThreeColorable G := by
  constructor
  · rintro ⟨n', G', h, hG'⟩
    have hd := decGraph_encGraph G
    rw [h, decGraph_encGraph] at hd
    cases hd
    exact hG'
  · intro h
    exact ⟨n, G, rfl, h⟩

/-! ### Edges -/

/-- The list of edges of `G`: the **ordered** pairs `(u, v)` with `G u v = true` (loops
included), in lexicographic order — the set `E` of [PS10, Protocol 127.5] in the formal model;
in the docstrings of `ThreeColoring/` the notation `|E|` means `edgeCount G = (edgeList G).length`.

**Deviation (run-3 audit P11-3):** `Graph n` is an arbitrary Boolean relation, so `E` is the
list of ordered pairs `(u, v)` with `G u v`; for a symmetric loopless graph (the text's
`G = (V, E)`) `edgeCount G = 2|E|`, one iteration of the protocol has soundness error
`1 − 1/(2|E|)` and the repeated protocol runs `n · edgeCount G = 2n|E|` iterations. The
verifier's challenge is uniform over the ordered pairs, i.e. uniform over the text's
undirected edges, and the bound `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged; a loop `(u, u)` is an
edge and makes the graph non-colourable, as it should. -/
def edgeList {n : ℕ} (G : Graph n) : List (Fin n × Fin n) :=
  (List.finRange n ×ˢ List.finRange n).filter fun p => G p.1 p.2

/-- The number `m` of (ordered) edge pairs of `G`, written `|E|` in the docstrings of
`ThreeColoring/` — for a symmetric loopless graph twice the `|E| = m` of
[PS10, Protocol 127.5] (see `edgeList`; run-3 audit P11-3). -/
abbrev edgeCount {n : ℕ} (G : Graph n) : ℕ := (edgeList G).length

/-- A pair is in the edge list iff it is an edge. -/
theorem mem_edgeList_iff {n : ℕ} (G : Graph n) (p : Fin n × Fin n) :
    p ∈ edgeList G ↔ G p.1 p.2 = true := by
  rcases p with ⟨u, v⟩
  simp [edgeList, List.mem_filter, List.mem_finRange]

/-- The edge of index `e : Fin |E|`. -/
def edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) : Fin n × Fin n := (edgeList G).get e

/-- The endpoints of `edgeOf G e` are adjacent. -/
theorem edgeOf_adj {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    G (edgeOf G e).1 (edgeOf G e).2 = true :=
  (mem_edgeList_iff G _).1 (List.get_mem _ _)

/-- Every edge is `edgeOf G e` for some index `e`. -/
theorem exists_edgeOf_eq {n : ℕ} (G : Graph n) {u v : Fin n} (h : G u v = true) :
    ∃ e : Fin (edgeCount G), edgeOf G e = (u, v) := by
  obtain ⟨e, he⟩ := List.mem_iff_get.1 ((mem_edgeList_iff G (u, v)).2 h)
  exact ⟨e, he⟩

/-- The edge of the (arbitrary) index `e : ℕ`, reduced modulo `|E|`; `none` iff `E = ∅`
(the total decoding of the verifier's challenge). -/
def edgeAt {n : ℕ} (G : Graph n) (e : ℕ) : Option (Fin n × Fin n) := (edgeList G)[e % edgeCount G]?

/-- On an in-range index `edgeAt` is `edgeOf`. -/
theorem edgeAt_eq_some_edgeOf {n : ℕ} (G : Graph n) (e : Fin (edgeCount G)) :
    edgeAt G e = some (edgeOf G e) := by
  unfold edgeAt edgeOf
  rw [Nat.mod_eq_of_lt e.isLt, List.getElem?_eq_getElem e.isLt, List.get_eq_getElem]

/-- The endpoints of `edgeAt G e` are adjacent. -/
theorem edgeAt_adj {n : ℕ} (G : Graph n) {e : ℕ} {p : Fin n × Fin n} (h : edgeAt G e = some p) :
    G p.1 p.2 = true :=
  (mem_edgeList_iff G p).1 (List.mem_of_getElem? h)

/-- With at least one edge every index decodes to an edge. -/
theorem edgeAt_isSome {n : ℕ} (G : Graph n) (hm : 0 < edgeCount G) (e : ℕ) :
    ∃ p, edgeAt G e = some p :=
  ⟨_, List.getElem?_eq_getElem (Nat.mod_lt _ hm)⟩

/-- `edgeAt` is `none` exactly when there are no edges. -/
theorem edgeAt_eq_none_iff {n : ℕ} (G : Graph n) (e : ℕ) : edgeAt G e = none ↔ edgeCount G = 0 := by
  constructor
  · intro h
    by_contra hm
    obtain ⟨p, hp⟩ := edgeAt_isSome G (Nat.pos_of_ne_zero hm) e
    rw [h] at hp
    exact Option.noConfusion hp
  · intro h
    unfold edgeAt
    rw [List.getElem?_eq_none_iff]
    change (edgeList G).length = 0 at h
    rw [h]
    exact Nat.zero_le _

/-- An edgeless graph is 3-colourable (constant colouring). -/
theorem threeColorable_of_edgeCount_eq_zero {n : ℕ} {G : Graph n} (h : edgeCount G = 0) :
    ThreeColorable G := by
  refine ⟨fun _ => 0, fun u v huv => ?_⟩
  have hmem := (mem_edgeList_iff G (u, v)).2 huv
  rw [List.length_eq_zero_iff.1 h] at hmem
  exact absurd hmem (List.not_mem_nil)

/-- A graph that is not 3-colourable has an edge. -/
theorem edgeCount_pos_of_not_threeColorable {n : ℕ} {G : Graph n} (h : ¬ ThreeColorable G) :
    0 < edgeCount G :=
  Nat.pos_of_ne_zero fun h0 => h (threeColorable_of_edgeCount_eq_zero h0)

/-! ### Claim-125.a -/

/-- `(1 - 1/m)^{n m} ≤ e^{-n}` for `m ≥ 1` [PS10, proof of Proposition 127.6,
"`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Claim-125.a): `Real.one_sub_div_pow_le_exp_neg` with `N := n m`
and `t := n`, after rewriting `n / (n m) = 1 / m`. -/
theorem one_sub_inv_pow_mul_le_exp (m n : ℕ) (hm : 0 < m) :
    (1 - 1 / (m : ℝ)) ^ (n * m) ≤ Real.exp (-(n : ℝ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have h := Real.one_sub_div_pow_le_exp_neg (n := n * m) (t := (n : ℝ))
    (by exact_mod_cast Nat.le_mul_of_pos_right n hm)
  have hnm : (n : ℝ) / ((n * m : ℕ) : ℝ) = 1 / m := by
    rw [Nat.cast_mul]
    field_simp
  rwa [hnm] at h

/-- `e^{-n} ≤ 2^{-n}` (the text's "`≈ e^{-n}`" bounded by the dyadic negligible function):
`2 ≤ e` by `Real.add_one_le_exp`. -/
theorem exp_neg_le_inv_two_pow (n : ℕ) : Real.exp (-(n : ℝ)) ≤ (2 : ℝ)⁻¹ ^ n := by
  rw [Real.exp_neg, show (n : ℝ) = n * 1 by ring, Real.exp_nat_mul, ← inv_pow]
  exact pow_le_pow_left₀ (by positivity)
    (inv_anti₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)])) n

/-! ### Colours as `n`-bit values (DQ4) -/

/-- The two-bit encoding of a colour (`encColoring` of a one-vertex colouring). -/
def encColor (a : Fin 3) : List Bool := encColoring fun _ : Fin 1 => a

/-- The total decoding of a colour from a string (`decColoring` at one vertex). -/
def decColor (w : List Bool) : Fin 3 := decColoring 1 w 0

/-- Decoding an encoded colour gives the colour back. -/
@[simp] theorem decColor_encColor (a : Fin 3) : decColor (encColor a) = a :=
  congrFun (decColoring_encColoring fun _ : Fin 1 => a) 0

/-- A colour padded to an `n`-bit value (DQ4): the two bits of `encColor a` followed by
zeros. The value committed to by the prover of [PS10, Protocol 127.5] at security parameter
`n`. -/
def padColor (n : ℕ) (a : Fin 3) : Fin n → Bool := padFin n (encColor a)

/-- The two-bit encodings of distinct colours differ in one of the two bits. -/
theorem encColor_getD_ne {a b : Fin 3} (hab : a ≠ b) :
    (encColor a).getD 0 false ≠ (encColor b).getD 0 false ∨
      (encColor a).getD 1 false ≠ (encColor b).getD 1 false := by
  revert a b
  decide

/-- Padding to `n ≥ 2` bits is injective on colours. -/
theorem padColor_injective {n : ℕ} (hn : 2 ≤ n) : Function.Injective (padColor n) := by
  intro a b h
  by_contra hab
  have h0 := congrFun h ⟨0, by omega⟩
  have h1 := congrFun h ⟨1, by omega⟩
  simp only [padColor, padFin] at h0 h1
  rcases encColor_getD_ne hab with hne | hne
  · exact hne h0
  · exact hne h1

/-! ### Samplers of the honest parties (D10) -/

/-- `T` rejection trials of `k` bits read consecutively from a tape (bit `j` of trial `t` at
position `t k + j`), the first accepted value in `Fin m` (`rejectionSample`, D10). -/
def sampleIdx (m k T : ℕ) (r : List Bool) : Option (Fin m) :=
  rejectionSample m k T fun t j => r.getD (t * k + j) false

/-- The six permutations of the three colours enumerated by `Fin 6`. -/
noncomputable def perm3Equiv : Fin 6 ≃ Equiv.Perm (Fin 3) :=
  (Fintype.equivFinOfCardEq (by rw [Fintype.card_perm, Fintype.card_fin]; rfl)).symm

/-- The honest prover's colour permutation `π ← S₃` of [PS10, Protocol 127.5] from the first
`3T` bits of its tape: `T` rejection trials of three bits (success probability `6/8` each),
the identity on failure (D10). -/
noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
  ((sampleIdx 6 3 T r).map perm3Equiv).getD 1

/-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
the index `0` on failure (D10). -/
def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
  ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0

/-- With at least one edge the sampled index is in range. -/
theorem sampleEdgeIdx_lt {m : ℕ} (hm : 0 < m) (T : ℕ) (r : List Bool) : sampleEdgeIdx m T r < m := by
  unfold sampleEdgeIdx
  cases sampleIdx m (Nat.size m) T r with
  | none => simpa using hm
  | some e => simp [e.isLt]

/-- The unary encoding of the verifier's challenge: the edge index `e` as `1^e`. -/
def edgeMsg (e : ℕ) : List Bool := List.replicate e true

/-- The total decoding of a challenge string as an edge index in `[m]`: its length modulo `m`
(every string names an edge when `E ≠ ∅`). -/
def edgeIdxOfMsg (m : ℕ) (w : List Bool) : ℕ := w.length % m

/-- The challenge `1^e` decodes to `e` when `e < m`. -/
@[simp] theorem edgeIdxOfMsg_edgeMsg {m e : ℕ} (he : e < m) : edgeIdxOfMsg m (edgeMsg e) = e := by
  simp [edgeIdxOfMsg, edgeMsg, Nat.mod_eq_of_lt he]

/-- The decoded index is in range when `m > 0`. -/
theorem edgeIdxOfMsg_lt {m : ℕ} (hm : 0 < m) (w : List Bool) : edgeIdxOfMsg m w < m :=
  Nat.mod_lt _ hm

/-- A tape of `T k` bits read as `T` trials of `k` bits: bit `j` of trial `t` is tape bit
`finProdFinEquiv (t, j) = t k + j` (the curried `finProdFinEquiv`). -/
private def tapeEquiv (T k : ℕ) : (Fin (T * k) → Bool) ≃ (Fin T → Fin k → Bool) where
  toFun r t j := r (finProdFinEquiv (t, j))
  invFun b i := b (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2
  left_inv r := by
    funext i
    simp only [Prod.mk.eta, Equiv.apply_symm_apply]
  right_inv b := by
    funext t j
    simp

/-- Bit `t k + j` of the tape `List.ofFn r` is entry `(t, j)` of its trial table. -/
private theorem ofFn_getD_tape {T k : ℕ} (r : Fin (T * k) → Bool) (t : Fin T) (j : Fin k) :
    (List.ofFn r).getD (t * k + j) false = tapeEquiv T k r t j := by
  have hm : ((finProdFinEquiv (t, j) : Fin (T * k)) : ℕ) = t * k + j := by
    simp only [finProdFinEquiv_apply_val]
    ring
  show _ = r (finProdFinEquiv (t, j))
  rw [← hm, List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (Fin.isLt _),
    Option.getD_some, Fin.eta]

/-- On a tape of exactly `T k` bits, `sampleIdx` is `rejectionSample` on the trial table. -/
private theorem sampleIdx_ofFn (m k T : ℕ) (r : Fin (T * k) → Bool) :
    sampleIdx m k T (List.ofFn r) = rejectionSample m k T (tapeEquiv T k r) := by
  unfold sampleIdx
  congr 1
  funext t j
  exact ofFn_getD_tape r t j

/-- The permutation sampler is within `(1/4)^T` of a uniform permutation of the colours (D10).

**Proof sketch.** `statClose_rejectionSample 6 3 T` (with `6 ≤ 2³`) gives closeness
`(1 - 6/8)^T = (1/4)^T` of `(rejectionSample 6 3 T b).getD d` to the identity on `Fin 6`; the
tape-to-trials map `r ↦ (t, j) ↦ r.getD (3t + j)` on `Fin (T * 3) → Bool` is the bijection
`finProdFinEquiv` curried (`StatClose.comp_equiv_left`), and `perm3Equiv` is a bijection
with `perm3Equiv d = 1` for the right default `d` (`StatClose.map`, `StatClose.comp_equiv_right`). -/
theorem statClose_samplePerm3 (T : ℕ) :
    StatClose (fun r : Fin (T * 3) → Bool => samplePerm3 T (List.ofFn r))
      (id : Equiv.Perm (Fin 3) → Equiv.Perm (Fin 3)) ((1 / 4 : ℝ) ^ T) := by
  have h := (((statClose_rejectionSample 6 3 T (by norm_num) (by norm_num)
    (perm3Equiv.symm 1)).map perm3Equiv).comp_equiv_right perm3Equiv.symm).comp_equiv_left
    (tapeEquiv T 3)
  have hδ : (1 - ((6 : ℕ) : ℝ) / 2 ^ 3) ^ T = (1 / 4) ^ T := by norm_num
  rw [hδ] at h
  convert h using 2 with r σ
  · simp only [samplePerm3, sampleIdx_ofFn]
    cases rejectionSample 6 3 T (tapeEquiv T 3 r) with
    | none => simp
    | some i => simp
  · simp

/-- The edge sampler is within `(1/2)^T` of a uniform edge index (D10).

**Proof sketch.** `statClose_rejectionSample m (Nat.size m) T` with `m ≤ 2^{size m}`
(`Nat.lt_size_self`) gives closeness `(1 - m/2^{size m})^T`; since `2^{size m} ≤ 2m` for
`m ≥ 1` (`Nat.size_le`, `Nat.lt_size`), `1 - m/2^{size m} ≤ 1/2` and `pow_le_pow_left₀`;
the tape-to-trials map is the curried `finProdFinEquiv` (`StatClose.comp_equiv_left`), and
`sampleEdgeIdx` is `Fin.val` of the sampler's `getD ⟨0, hm⟩`. -/
theorem statClose_sampleEdgeIdx {m : ℕ} (hm : 0 < m) (T : ℕ) :
    StatClose (fun r : Fin (T * Nat.size m) → Bool =>
        (⟨sampleEdgeIdx m T (List.ofFn r), sampleEdgeIdx_lt hm T _⟩ : Fin m))
      (id : Fin m → Fin m) ((1 / 2 : ℝ) ^ T) := by
  have hk : m ≤ 2 ^ Nat.size m := (Nat.lt_size_self m).le
  have hpos : 0 < Nat.size m := Nat.size_pos.2 hm
  have h1 : 2 ^ (Nat.size m - 1) ≤ m := Nat.lt_size.1 (Nat.sub_lt hpos one_pos)
  have h2 : 2 ^ Nat.size m ≤ 2 * m := by
    have : 2 ^ Nat.size m = 2 * 2 ^ (Nat.size m - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  have h := (statClose_rejectionSample m (Nat.size m) T hm hk ⟨0, hm⟩).comp_equiv_left
    (tapeEquiv T (Nat.size m))
  have h2k : (0 : ℝ) < 2 ^ Nat.size m := by positivity
  have hm' : (m : ℝ) ≤ 2 ^ Nat.size m := by exact_mod_cast hk
  have h2' : (2 : ℝ) ^ Nat.size m ≤ 2 * m := by exact_mod_cast h2
  have hle : (1 - (m : ℝ) / 2 ^ Nat.size m) ^ T ≤ (1 / 2 : ℝ) ^ T := by
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact hm'
    · have : (1 / 2 : ℝ) ≤ m / 2 ^ Nat.size m := by
        rw [div_le_div_iff₀ (by norm_num) h2k]
        linarith
      linarith
  convert h.mono hle using 2 with r
  apply Fin.ext
  simp only [sampleEdgeIdx, sampleIdx_ofFn]
  cases rejectionSample m (Nat.size m) T (tapeEquiv T (Nat.size m) r) with
  | none => simp
  | some i => simp

end TCSlib.Cryptography
