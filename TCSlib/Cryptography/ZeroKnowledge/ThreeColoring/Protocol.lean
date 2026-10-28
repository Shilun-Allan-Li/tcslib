/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the protocol, completeness and soundness

The protocol of [PS10, Protocol 127.5] for the language `3COL` of `ThreeColoring/Language.lean`
(Def-124.f), built on a commitment scheme
`(Com, ℓ)` of `Commitment.lean`, and the completeness and soundness halves of
[PS10, Proposition 127.6]: one iteration (soundness error `1 - 1/|E|`) and the `n|E|`-fold
sequential repetition (soundness error `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`, Claim-125.a). The
zero-knowledge half is `ThreeColoring/Simulator.lean`; the machine infrastructure behind the
efficiency theorems (the parties as polynomial-time string functions of the interactive
layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`.

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours; the edges
are enumerated by `edgeList` and the verifier's challenge is the index of an edge in that
list, sent in unary. The prover commits to the colour `π (c i)` of every vertex, padded to an
`n`-bit value (`padColor`, DQ4), with `n` the number of vertices as the security parameter of
the commitment.

**Deviations** ([PS10, Protocol 127.5], source errors 41–43 of the plan):
* the verifier checks the two openings against the commitments (the text's "`V` accepts iff
  `c'_i ≠ c'_j`" is unsound without it) and the lengths of the opening randomness;
* if `E = ∅` the verifier accepts outright (every edgeless graph is 3-colourable; the text's
  "random edge" is undefined), and if `E ≠ ∅` but the graph has fewer than two vertices (so
  the edge is a loop and the graph is not colourable) it rejects outright, which is what makes
  the `n`-bit padding of the colours injective in every case that matters;
* colours are padded to `n` bits (DQ4; the text commits to 2-bit colours, i.e. at security
  parameter `2`);
* the witness is `c₁, …, c_n` (the text lists `c₀, …, c_m`), and the protocol is repeated
  `n|E|` times (the text's proof says `|E|²`);
* (D8, D10) the colour permutation `π ← S₃` and the edge `e ← E` are rejection-sampled from
  the parties' bit tapes with `|x|` trials, so the theorems carry the statistical terms
  `(1/4)^{|x|}` and `(1/2)^{|x|}`; the repeated protocol runs `4|x|²` fixed moves of which the
  first `4 n|E|` are the iterations and the rest are empty messages;
* (run-3 audit P11-3) `Graph n` is an arbitrary Boolean relation and `E` is the list of
  ordered pairs `(u, v)` with `G u v` (`edgeList`, loops included), so for the text's
  symmetric loopless graph `edgeCount G = 2|E|`: the per-iteration soundness error
  `1 - 1/edgeCount G` is `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|`
  times; the challenge is uniform over the ordered pairs, i.e. over the text's undirected
  edges, and `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. In this file `|E|` abbreviates
  `edgeCount G`.

## Main definitions

* `TCSlib.Cryptography.colCommit`,
  `TCSlib.Cryptography.colOpen`, `TCSlib.Cryptography.colVerify` — the commitment message,
  the opening message and the verifier's check of one iteration.
* `TCSlib.Cryptography.colProver`, `TCSlib.Cryptography.colVerifier`,
  `TCSlib.Cryptography.colProtocol` — one iteration of [PS10, Protocol 127.5];
  `TCSlib.Cryptography.colProverRep`, `TCSlib.Cryptography.colVerifierRep`,
  `TCSlib.Cryptography.colProtocolRep` — the `n|E|`-fold protocol (Prot-127.5).
* `TCSlib.Cryptography.committedColor` — the colour a commitment string can be opened to
  (Lem-127.f).

## Main results

* `TCSlib.Cryptography.colVerify_honest` — completeness of one iteration (Claim-127.e).
* `TCSlib.Cryptography.committedColor_eq_some`, `TCSlib.Cryptography.exists_bad_edge` — the
  committed colouring and its bad edge (Lem-127.f).
* `TCSlib.Cryptography.uprob_adaptive_escape` — adaptive sequential soundness with escape
  probability `1/m` (Lem-127.g); `TCSlib.Cryptography.uprob_col_cheat_le` — soundness of the
  `k`-fold protocol against adaptive provers (Claim-127.h).
* `TCSlib.Cryptography.col_efficientProverProofErr`,
  `TCSlib.Cryptography.colRep_efficientProverProof` — **[PS10, Proposition 127.6]**, the
  interactive-proof half (Prop-127.6).
* `TCSlib.Cryptography.R3COL_witnessRelation` — `R_3COL` is a witness relation for `3COL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring; Chapter 9, zero knowledge.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Messages of one iteration -/

/-- The `i`-th component of an encoded message list (`Strategy.encodeMsgs`): the first
projection after `i` second projections. -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- `msgAt` reads the `i`-th message of an encoded list. -/
theorem msgAt_encodeMsgs (l : List (List Bool)) (i : ℕ) (hi : i < l.length) :
    msgAt (Strategy.encodeMsgs l) i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a l ih =>
    cases i with
    | zero => simp [msgAt]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [msgAt, Function.iterate_succ_apply] using this

/-- The prover's first message of [PS10, Protocol 127.5]: the commitments to the (permuted)
colours `c' i`, padded to `n` bits, with randomness `r i ∈ {0,1}^{ℓ(n)}`, as one encoded list
(`multiCom`). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- The prover's opening message of [PS10, Protocol 127.5] for the edge `p = (i, j)`:
`⟨⟨c'_i, r_i⟩, ⟨c'_j, r_j⟩⟩`. -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- The verifier's check of one iteration of [PS10, Protocol 127.5] on the edge of index `e`,
the commitment message `com` and the opening `opn = ⟨⟨a, r_i⟩, ⟨b, r_j⟩⟩`: the randomness has
length `ℓ(n)`, both openings match the commitments, and `a ≠ b`.

**Deviation:** the opening check (the text's "`V` accepts iff `c'_i ≠ c'_j`"); `false` when
`E = ∅` (handled by the verifier before calling this check). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- **Completeness of one iteration** [PS10, proof of Proposition 127.6, "completeness follows
by inspection"] (Claim-127.e): for a proper colouring `c`, any colour permutation `π`, any
randomness `r` and any edge `p = edgeAt G e`, the honest commitment and opening pass the
verifier's check: the openings match by `msgAt_encodeMsgs`, and `π (c i) ≠ π (c j)` since
`c i ≠ c j` on the edge and `π` is injective. -/
theorem colVerify_honest (Com : List Bool → List Bool) {n ℓn : ℕ} {G : Graph n}
    {c : Fin n → Fin 3} (hc : ProperColoring G c) (π : Equiv.Perm (Fin 3))
    (r : Fin n → Fin ℓn → Bool) {e : ℕ} {p : Fin n × Fin n} (hp : edgeAt G e = some p) :
    colVerify Com ℓn G e (colCommit Com n ℓn (fun i => π (c i)) r)
      (colOpen (fun i => π (c i)) r p) = true := by
  have hadj := edgeAt_adj G hp
  unfold colVerify
  rw [hp]
  simp only [colOpen, pairFstD_pairEncode, pairSndD_pairEncode, decColor_encColor,
    List.length_ofFn, decide_eq_true_eq]
  refine ⟨trivial, trivial, ?_, ?_, fun h => hc _ _ hadj (π.injective h)⟩
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The committed colouring (Lem-127.f) -/

/-- The colour a commitment string `w` can be opened to at security parameter `n` with
randomness of length `ℓn` (Lem-127.f): `some a` if some `(a, r)` opens `w`, `none` otherwise.
By binding (`committedColor_eq_some`) the colour is unique. -/
noncomputable def committedColor (Com : List Bool → List Bool) (n ℓn : ℕ) (w : List Bool) :
    Option (Fin 3) := by
  classical
  exact if h : ∃ a : Fin 3, ∃ r : Fin ℓn → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w
    then some (Classical.choose h) else none

/-- A list of length `k` is the `ofFn` of its entries read with a default. -/
private theorem ofFn_getD_of_length {r : List Bool} {k : ℕ} (hr : r.length = k) :
    List.ofFn (fun i : Fin k => r.getD i false) = r := by
  subst hr
  exact List.ext_getElem (by simp) fun i _ h₂ => by
    simp [List.getD_eq_getElem?_getD]

/-- **The committed colouring is well defined** [PS10, proof of Proposition 127.6,
"soundness follows by the binding property"] (Lem-127.f): for a commitment scheme, `n ≥ 2`,
an opening `(a, r)` of `w` with `|r| = ℓ(n)` forces `committedColor w = some a` — any other
opening `(a', r')` would give `Com ⟨pad a', r'⟩ = Com ⟨pad a, r⟩` with `pad a' ≠ pad a`
(`padColor_injective`), contradicting `Commitment.binding_ofFn`. -/
theorem committedColor_eq_some {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {a : Fin 3} {r : List Bool}
    (hr : r.length = ℓ.eval n) {w : List Bool}
    (h : Com (pairEncode (List.ofFn (padColor n a)) r) = w) :
    committedColor Com n (ℓ.eval n) w = some a := by
  classical
  have hex : ∃ a : Fin 3, ∃ r : Fin (ℓ.eval n) → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w :=
    ⟨a, fun i => r.getD i false, by rwa [ofFn_getD_of_length hr]⟩
  unfold committedColor
  rw [dif_pos hex, Option.some.injEq]
  obtain ⟨r', hr'⟩ := Classical.choose_spec hex
  by_contra hne
  have hpad : padColor n (Classical.choose hex) ≠ padColor n a :=
    fun h' => hne (padColor_injective hn h')
  have := hC.binding_ofFn hpad r' (fun i => r.getD i false)
  rw [ofFn_getD_of_length hr, hr', h] at this
  exact this rfl

/-- **A non-colourable graph has a bad edge for every partial colouring**
[PS10, proof of Proposition 127.6, "for each coloring there exists at least one edge which
has the same colors on both endpoints"] (Lem-127.f): if `G` is not 3-colourable then for every
`ct : Fin n → Option (Fin 3)` some edge has an uncoloured endpoint or equal colours at both
endpoints — otherwise `i ↦ (ct i).getD 0` would be a proper colouring. -/
theorem exists_bad_edge {n : ℕ} {G : Graph n} (hG : ¬ ThreeColorable G)
    (ct : Fin n → Option (Fin 3)) :
    ∃ e : Fin (edgeCount G), ct (edgeOf G e).1 = none ∨ ct (edgeOf G e).2 = none ∨
      ct (edgeOf G e).1 = ct (edgeOf G e).2 := by
  by_contra hcon
  push_neg at hcon
  refine hG ⟨fun i => (ct i).getD 0, fun u v huv heq => ?_⟩
  obtain ⟨e, he⟩ := exists_edgeOf_eq G huv
  obtain ⟨h1, h2, h3⟩ := hcon e
  simp only [he] at h1 h2 h3
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 h2
  simp only [ha, hb] at h3 heq
  exact h3 (by simpa using heq)

/-! ### Adaptive sequential soundness (Lem-127.g, Claim-127.h) -/

/-- The strict prefix `e_0, …, e_{i-1}` of a challenge tuple (the history an adaptive prover
has seen before challenge `i`). -/
def challengesBefore {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin i → α :=
  fun j => e (Fin.castLE i.isLt.le j)

/-- The prefix `e_0, …, e_i` of a challenge tuple (the history including the current
challenge). -/
def challengesUpTo {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin (i + 1) → α :=
  fun j => e (Fin.castLE i.isLt j)

/-- A `(k+1)`-tuple of challenges with auxiliary data as a `k`-tuple, the data and the last
challenge (`Fin.snoc`): the splitting of the sequential-soundness induction. -/
private def snocEquivW (k m : ℕ) (W : Type*) :
    ((Fin k → Fin m) × W) × Fin m ≃ (Fin (k + 1) → Fin m) × W where
  toFun y := (Fin.snoc y.1.1 y.2, y.1.2)
  invFun z := ((Fin.init z.1, z.2), z.1 (Fin.last k))
  left_inv y := by
    rcases y with ⟨⟨e, w⟩, x⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    rcases z with ⟨e, w⟩
    simp [Fin.snoc_init_self]

/-- The history before a non-final challenge of `Fin.snoc e x` is the history before it in `e`. -/
private theorem challengesBefore_snoc_castSucc {k m : ℕ} (e : Fin k → Fin m) (x : Fin m)
    (i : Fin k) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.castSucc i) =
      challengesBefore e i := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (k + 1)) =
      Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- The history before the last challenge of `Fin.snoc e x` is `e`. -/
private theorem challengesBefore_snoc_last {k m : ℕ} (e : Fin k → Fin m) (x : Fin m) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.last k) = e := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.last k).isLt.le j : Fin (k + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- **Adaptive sequential soundness with escape probability `1/m`** [PS10, proof of
Proposition 127.6, "in each iteration a cheating prover is caught with probability `1/|E|`"]
(Lem-127.g): for `k` rounds with uniform challenges `e_i ∈ [m]` and, for every round, a
nonempty set `Bad i` of challenges (depending on the earlier challenges and on the prover's
coins `w`) on which the prover is caught, the probability that no challenge ever lands in its
bad set is at most `(1 - 1/m)^k`.

**Proof sketch.** Induction on `k`. Split the tuple as `Fin.snoc e' e_last` (the bijection
`(Fin (k+1) → Fin m) ≃ (Fin k → Fin m) × Fin m`, `Fin.snocEquiv`; `uprob_comp_equiv`); by
`uprob_prod` the probability is the average over `(e', w)` of the probability over `e_last`,
which is `0` if some earlier round is caught and at most `1 - |Bad k e' w| / m ≤ 1 - 1/m` otherwise
(`uprob_eq_card_filter`, `Finset.card_pos` from `hBad`); so the total is at most `(1 - 1/m)`
times the probability of the `k`-round event (`OneWay.uprob_and_le_mul`), and the induction
hypothesis applies to the latter. -/
theorem uprob_adaptive_escape (m k : ℕ) (hm : 0 < m) {W : Type*} [Fintype W]
    (Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m))
    (hBad : ∀ i h w, (Bad i h w).Nonempty) :
    uprob (fun z : (Fin k → Fin m) × W => ∀ i, z.1 i ∉ Bad i (challengesBefore z.1 i) z.2) ≤
      (1 - 1 / (m : ℝ)) ^ k := by
  induction k with
  | zero => simpa using uprob_le_one _
  | succ k ih =>
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hθ : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm']
      exact_mod_cast hm
    have hih := ih (fun i h w => Bad (Fin.castSucc i) h w) (fun i h w => hBad _ _ _)
    rw [← uprob_comp_equiv (snocEquivW k m W)]
    have hmono : uprob (fun y : ((Fin k → Fin m) × W) × Fin m => ∀ i,
          ((snocEquivW k m W) y).1 i ∉
            Bad i (challengesBefore ((snocEquivW k m W) y).1 i) ((snocEquivW k m W) y).2) ≤
        uprob (fun y : ((Fin k → Fin m) × W) × Fin m =>
          (∀ i, y.1.1 i ∉ Bad (Fin.castSucc i) (challengesBefore y.1.1 i) y.1.2) ∧
            y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2) := by
      apply uprob_mono
      rintro ⟨⟨e, w⟩, x⟩ h
      refine ⟨fun i => ?_, ?_⟩
      · have := h (Fin.castSucc i)
        simpa [snocEquivW, Fin.snoc_castSucc, challengesBefore_snoc_castSucc] using this
      · have := h (Fin.last k)
        simpa [snocEquivW, Fin.snoc_last, challengesBefore_snoc_last] using this
    have hbound := OneWay.uprob_and_le_mul
      (fun a : (Fin k → Fin m) × W => ∀ i, a.1 i ∉ Bad (Fin.castSucc i) (challengesBefore a.1 i) a.2)
      (fun y : ((Fin k → Fin m) × W) × Fin m => y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2)
      (θ := 1 - 1 / (m : ℝ)) (fun a _ => ?_)
    · calc _ ≤ _ := hmono
        _ ≤ _ := hbound
        _ ≤ (1 - 1 / (m : ℝ)) * (1 - 1 / (m : ℝ)) ^ k := mul_le_mul_of_nonneg_left hih hθ
        _ = (1 - 1 / (m : ℝ)) ^ (k + 1) := by ring
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      classical
      rw [uprob_not, uprob_eq_card_filter, Fintype.card_fin]
      have hcard : 1 ≤ (Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.card_pos.2 (hBad _ _ _)
      have : (1 : ℝ) / m ≤
          ((Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card : ℝ) / m := by
        gcongr
        exact_mod_cast hcard
      linarith

/-- **Soundness of the `k`-fold protocol against adaptive provers** [PS10, proof of
Proposition 127.6] (Claim-127.h, concrete): for a commitment scheme, a graph on `n ≥ 2`
vertices that is not 3-colourable, and a cheating prover whose `i`-th commitment message
`comF i` depends on the earlier challenges and its coins `w`, and whose `i`-th opening
`opnF i` also depends on the current challenge, the verifier accepts all `k` iterations with
probability at most `(1 - 1/|E|)^k` over the uniform challenges and `w` (`|E| = edgeCount G`,
the number of ordered edge pairs; run-3 audit P11-3).

**Proof sketch.** Apply `uprob_adaptive_escape` with
`Bad i h w := {e | the edge `edgeOf G e` is bad for the committed colouring
`k ↦ committedColor Com n ℓ(n) (msgAt (comF i h w) k)`}`, nonempty by `exists_bad_edge`
(`edgeCount_pos_of_not_threeColorable`). Acceptance in round `i` on the challenge `e_i`
means (`colVerify`, `edgeAt_eq_some_edgeOf`) that both openings `(a, r_i)`, `(b, r_j)` have
randomness of length `ℓ(n)` and match the commitments at the endpoints, so by
`committedColor_eq_some` the committed colours at the endpoints are `some a`, `some b` with
`a ≠ b`: the edge is not bad, i.e. `e_i ∉ Bad i …`. Hence the acceptance event is contained
in the escape event (`uprob_mono`). -/
theorem uprob_col_cheat_le {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G) (k : ℕ) {W : Type*} [Fintype W]
    (comF : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → List Bool)
    (opnF : (i : Fin k) → (Fin (i + 1) → Fin (edgeCount G)) → W → List Bool) :
    uprob (fun z : (Fin k → Fin (edgeCount G)) × W => ∀ i,
      colVerify Com (ℓ.eval n) G (z.1 i) (comF i (challengesBefore z.1 i) z.2)
        (opnF i (challengesUpTo z.1 i) z.2) = true) ≤
      (1 - 1 / (edgeCount G : ℝ)) ^ k := by
  classical
  have hm := edgeCount_pos_of_not_threeColorable hG
  let ct : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Fin n → Option (Fin 3) :=
    fun i h w v => committedColor Com n (ℓ.eval n) (msgAt (comF i h w) v)
  let Bad : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Finset (Fin (edgeCount G)) :=
    fun i h w => Finset.univ.filter fun e => ct i h w (edgeOf G e).1 = none ∨
      ct i h w (edgeOf G e).2 = none ∨ ct i h w (edgeOf G e).1 = ct i h w (edgeOf G e).2
  have hBad : ∀ i h w, (Bad i h w).Nonempty := by
    intro i h w
    obtain ⟨e, he⟩ := exists_bad_edge hG (ct i h w)
    exact ⟨e, by simpa [Bad] using he⟩
  refine le_trans (uprob_mono ?_) (uprob_adaptive_escape (edgeCount G) k hm Bad hBad)
  rintro ⟨es, w⟩ hacc i
  have h := hacc i
  simp only at h ⊢
  unfold colVerify at h
  rw [edgeAt_eq_some_edgeOf] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hri, hrj, hci, hcj, hab⟩ := h
  have h1 := committedColor_eq_some hC hn hri hci
  have h2 := committedColor_eq_some hC hn hrj hcj
  simp only [Bad, ct, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  rw [h1, h2]
  simp [hab]

/-! ### Protocol 127.5, one iteration (Prot-127.5) -/

/-- The well-formedness test of a common input: `x` is the encoding of the graph it decodes
to (i.e. `|x|` is a perfect square). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- An encoded graph is well formed. -/
theorem colWellFormed_encGraph {n : ℕ} (G : Graph n) : colWellFormed (encGraph G) = true := by
  unfold colWellFormed
  rw [decide_eq_true_eq]
  have h := decGraph_encGraph G
  rw [show encGraph (decGraph (encGraph G)).2 = encGraph (⟨n, G⟩ : Σ n, Graph n).2 by rw [h]]

/-- The honest prover of one iteration of [PS10, Protocol 127.5] (Prot-127.5): with common
input `x = encGraph G` (`n` vertices) and witness `y = encColoring c`, it samples `π ← S₃` from
the first `3|x|` bits of its tape and `r_i ∈ {0,1}^{ℓ(n)}` from the next `n ℓ(n)` bits; on the
empty history it sends the commitments to `π (c i)` (`colCommit`), and on the challenge `w`
it opens the two commitments of the edge `edgeAt G (edgeIdxOfMsg |E| w)` (`colOpen`), or
sends `[]` if `E = ∅`. Coins: `3|x| + |x| ℓ(|x|)` bits (an upper bound for every `n ≤ |x|`).

**Deviation (D10):** `π` by rejection sampling (identity on failure). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- The verifier of one iteration of [PS10, Protocol 127.5] (Prot-127.5): it samples the
edge index `e ← [|E|]` from its tape (`sampleEdgeIdx` with `|x|` trials); on the commitment
message it sends `1^e`; on the complete history `[com, opn]` it outputs `[true]` iff `x` is
well formed and either `E = ∅` or (`n ≥ 2` and `colVerify` accepts the openings on the edge
`e`). Coins: `(|x| + 1)²` bits.

**Deviation:** opening check, `E = ∅` accepted outright, `n < 2` with `E ≠ ∅` rejected outright,
well-formedness test (see the module docstring); `e` by rejection sampling (D10). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- One iteration of [PS10, Protocol 127.5] (Prot-127.5): three messages (commitments,
edge, openings), prover first; the verdict is the verifier's activation on `[com, opn]`. -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-! ### The `n|E|`-fold protocol (Prot-127.5, repeated) -/

/-- The `t`-th block of `c` bits of a tape (the coins of iteration `t` of the repeated
protocol). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- The number of iterations of the repeated protocol on `x`: `n |E|` [PS10, Protocol 127.5,
"repeat the procedure `n|E|` times"], with `|E| = edgeCount G` the number of ordered edge
pairs (for the text's simple graph `2n|E|` iterations; run-3 audit P11-3). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- The prover of the `n|E|`-fold protocol: iteration `t = hist.length / 2` (it has received
the challenges and the empty verifier messages of the earlier iterations) runs `colProver`
on the `t`-th block of `3|x| + |x| ℓ(|x|)` coins; after the `n|E|` iterations it sends `[]`. -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- The verifier of the `n|E|`-fold protocol: it has received `[com_0, opn_0, com_1, …]`; on
an odd history it sends the challenge of iteration `t = hist.length / 2` (from the `t`-th
block of `(|x|+1)²` coins); on the complete history (`2|x|²` received messages) it accepts iff
`x` is well formed and either `E = ∅` or `n ≥ 2` and every one of the `n|E|` iterations passes
`colVerify`; on every other even history it sends `[]`. -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of one iteration is a PPT strategy when `Com` is polynomial-time
[PS10, Proposition 127.6, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^N, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`): `n = Nat.sqrt |x|`
in unary by `polyTimeComputable_iterateFind` over `polyTimeComputable_lenLe` against unary
squares; `π` by `polyTimeComputable_iterateFind` over the `|x|` three-bit trials
(`pairTakePoly`/`pairDropPoly`); the `n` commitments by `polyTimeComputable_blockMap ℓ` on
the randomness blocks composed with `hCom` on `⟨pad (π (c i)), r_i⟩` (`PolyTimeComputable.pairEncode`,
the colour permutation as a table lookup, `polyTimeComputable_ite`) and
`polyTimeComputable_iterateEmit` for the `encodeMsgs` fold; the opening by the two projections
of the challenge's decoded index (`polyTimeComputable_lenLe` against the unary `|E|`, the edge
list scanned by `polyTimeComputable_iterateFind`); the case split on `msgs = []` by
`polyTimeComputable_lenEq`. The equation with `colProver.next` is
`NUPPT.runAtL_ofPolyTimeUniform` and `Strategy.pairFstD_encodeMsgs`. -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  ColProofs.colProver_efficient hCom ℓ

/-- The verifier of one iteration is a PPT strategy when `Com` is polynomial-time
[PS10, Definition 116.1 for Proposition 127.6] (Inf-4.2).

**Proof sketch.** As `colProver_efficient`: the edge index by `polyTimeComputable_iterateFind`
over the `|x|` trials of `Nat.size |E|` bits (`|E|` in unary by scanning the matrix with
`polyTimeComputable_iterateEmit`), the challenge `1^e` by `polyTimeComputable_unaryPoly`-style
emission, and the verdict by `polyTimeComputable_and` of the well-formedness test
(`polyTimeComputable_pairEq` on `x` and the re-encoded matrix), the two commitment checks
(`hCom` on the parsed openings, `msgAt` by `polyTimeComputable_iterate_pairFstD`-style
projections, `polyTimeComputable_pairEq`), the length tests (`polyTimeComputable_lenEq`) and
the colour comparison. -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  ColProofs.colVerifier_efficient hCom ℓ

/-- The prover of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): `colProver_efficient`
on the coin block `hist.length / 2` cut by `pairTakePoly`/`pairDropPoly`, with the parity and
iteration tests by `polyTimeComputable_lenLe` on unary counters. -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  ColProofs.colProverRep_efficient hCom ℓ

/-- The verifier of the `n|E|`-fold protocol is a PPT strategy (Inf-4.2): the challenge as in
`colVerifier_efficient` on the block `hist.length / 2`, and the verdict a loop over the
`n|E|` pairs of the history (`polyTimeComputable_iterate` with an accumulated conjunction of
`colVerify` checks). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  ColProofs.colVerifierRep_efficient hCom ℓ

/-! ### Proposition 127.6, interactive-proof half -/

section OneIteration

open ColMachines

/-! ### Unfolding the parties on a decoded instance -/

/-- The verifier's verdict on `[com, opn]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_two_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com opn : List Bool) :
    (colVerifier Com ℓ).next x z r [com, opn] =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length r) com opn = true)))] := by
  show [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
    colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
      (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) com opn = true)))] = _
  rw [hx]

/-- The verifier's challenge on `[com]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_one_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com : List Bool) :
    (colVerifier Com ℓ).next x z r [com] = edgeMsg (sampleEdgeIdx (edgeCount G) x.length r) := by
  show edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) = _
  rw [hx]

/-- The prover's commitments, on an input decoding to `⟨n, G⟩`. -/
private theorem colProver_next_nil_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) :
    (colProver Com ℓ).next x y r [] = colCommit Com n (ℓ.eval n)
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false) := by
  show colCommit Com (decGraph x).1 (ℓ.eval (decGraph x).1)
    (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i))
    (fun i j => r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) = _
  rw [hx]

/-- The prover's opening, on an input decoding to `⟨n, G⟩` with at least one edge. -/
private theorem colProver_next_cons_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List Bool)
    (h : List (List Bool)) :
    (colProver Com ℓ).next x y r (w :: h) = colOpen
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun (i : Fin n) (j : Fin (ℓ.eval n)) => r.getD (3 * x.length + i * ℓ.eval n + j) false)
      (edgeOf G ⟨edgeIdxOfMsg (edgeCount G) w % edgeCount G, Nat.mod_lt _ hm⟩) := by
  simp only [colProver]
  rw [hx]
  dsimp only
  rw [edgeAt_eq_some_of_pos G hm]

/-- The verdict of one iteration against any prover `P'`: the verifier's activation on the
two prover messages, the second being the reply to the challenge. -/
private theorem colProtocol_outV (Com : List Bool → List Bool) (ℓ : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (colProtocol Com ℓ).ExecCoins P' x) :
    (colProtocol Com ℓ).outV P' x y z r =
      (colVerifier Com ℓ).next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1)
            [(colVerifier Com ℓ).next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := rfl

/-! ### Completeness -/

/-- **The honest execution accepts** on every pair of random tapes: for a proper colouring the
verdict is `[true]`. -/
private theorem colProtocol_outV_honest {Com : List Bool → List Bool} {ℓ : PolyExpr} {n : ℕ}
    {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c) (z : List Bool)
    (r : (colProtocol Com ℓ).ExecCoins (colProtocol Com ℓ).P (encGraph G)) :
    (colProtocol Com ℓ).outV (colProtocol Com ℓ).P (encGraph G) (encColoring c) z r = [true] := by
  have hx : decGraph (encGraph G) = ⟨n, G⟩ := decGraph_encGraph G
  rw [colProtocol_outV]
  show (colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ [], (colProver Com ℓ).next _ _ _
    [(colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ []]]] = _
  rw [colVerifier_next_one_of Com ℓ hx, colProver_next_nil_of Com ℓ hx, colVerifier_next_two_of Com ℓ hx,
    colWellFormed_encGraph, decColoring_encColoring]
  by_cases hm : edgeCount G = 0
  · simp [hm]
  · have hpos := Nat.pos_of_ne_zero hm
    have he := sampleEdgeIdx_lt hpos (encGraph G).length (List.ofFn r.2)
    rw [colProver_next_cons_of Com ℓ hx hpos, decColoring_encColoring]
    simp only [edgeIdxOfMsg_edgeMsg he]
    rw [colVerify_honest Com hc _ _ (edgeAt_eq_some_of_pos G hpos _)]
    simp [ColProofs.two_le_of_edge hc hpos]

/-! ### Soundness -/

/-- **One-round soundness bound against a deterministic prover:** for a non-colourable graph
on `n ≥ 2` vertices, the verifier's check on a uniform edge index `e`, a fixed commitment
message and an opening depending on `e`, passes with probability at most `1 - 1/|E|`
(`uprob_col_cheat_le` at `k = 1`). -/
private theorem uprob_check_uniform_le {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G)
    (com : List Bool) (opn : ℕ → List Bool) :
    uprob (fun e : Fin (edgeCount G) => colVerify Com (ℓ.eval n) G e com (opn e) = true) ≤
      1 - 1 / (edgeCount G : ℝ) := by
  have h := uprob_col_cheat_le hC hn hG 1 (W := Unit) (fun _ _ _ => com)
    (fun i h _ => opn (h (Fin.last i)))
  rw [pow_one] at h
  refine le_trans ?_ h
  rw [← uprob_comp_equiv (ColProofs.finOneEquiv (edgeCount G))]
  apply uprob_mono
  intro e he i
  rw [Fin.fin_one_eq_zero i]
  exact he

/-- **Soundness of one iteration** [PS10, Proposition 127.6]: for `x ∉ 3COL` and any prover,
the verifier rejects with probability at least `1 - (1 - 1/|x| + (1/2)^{|x|})`. -/
private theorem colProtocol_sound {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    (x : List Bool) (hx : x ∉ L3COL) (P' : Strategy) (z : List Bool) :
    1 - (1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length) ≤
      uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
        (colProtocol Com ℓ).outV P' x [] z r = [false]) := by
  have hs0 : (0 : ℝ) ≤ 1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length := by
    have h1 : 1 / (x.length : ℝ) ≤ 1 := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h]; simp
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.length := by positivity
    linarith
  -- reduce to a bound on the acceptance probability
  suffices key : uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
      ¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ≤
        1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length by
    rw [uprob_not] at key
    linarith
  set n := (decGraph x).1 with hn_def
  set G := (decGraph x).2 with hG_def
  have hx' : decGraph x = ⟨n, G⟩ := rfl
  have hout : ∀ r : (colProtocol Com ℓ).ExecCoins P' x, (colProtocol Com ℓ).outV P' x [] z r =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
          (P'.next x [] (List.ofFn r.1) [])
          (P'.next x [] (List.ofFn r.1)
            [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true)))] := by
    intro r
    rw [colProtocol_outV, colVerifier_next_one_of Com ℓ hx', colVerifier_next_two_of Com ℓ hx']
  by_cases hwf : colWellFormed x = true
  · have hxG : x = encGraph G := of_decide_eq_true hwf
    have hnc : ¬ ThreeColorable G := fun h => hx (hxG ▸ (encGraph_mem_L3COL_iff G).2 h)
    have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hnc
    by_cases hn : 2 ≤ n
    · -- the acceptance event is the verifier's check
      have hacc : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          (¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ↔
            colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
              (P'.next x [] (List.ofFn r.1) [])
              (P'.next x [] (List.ofFn r.1)
                [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true := by
        intro r
        rw [hout r]
        simp [hwf, hm.ne', hn]
      -- fix the prover's coins
      obtain ⟨rP, hrP⟩ := (colProtocol Com ℓ).exists_proverCoins_le P' x [] z fun o => ¬ o = [false]
      refine hrP.trans ?_
      rw [OneWay.uprob_congr fun rV => hacc (rP, rV)]
      -- the sampled edge is close to uniform on the verifier's tape
      have hmx : edgeCount G ≤ x.length := by
        have h1 : x.length = n * n := by rw [hxG, length_encGraph]
        rw [edgeCount_eq G x (decGraph_apply x), h1]
        exact countTrue_le _ _
      have hle : x.length * Nat.size (edgeCount G) ≤ (colVerifier Com ℓ).coinLen x.length := by
        show x.length * Nat.size (edgeCount G) ≤ 1 * (x.length + 1) ^ 2
        have h1 : Nat.size (edgeCount G) ≤ x.length :=
          (Nat.size_le_size hmx).trans (Nat.size_le.2 Nat.lt_two_pow_self)
        calc x.length * Nat.size (edgeCount G) ≤ x.length * x.length := Nat.mul_le_mul_left _ h1
          _ ≤ 1 * (x.length + 1) ^ 2 := by nlinarith
      have hclose := (statClose_sampleEdgeIdx hm x.length).comp_pushesUniform
        (ColProofs.pushesUniform_castLE hle)
      have hbound := hclose.uprob_le_add fun e : Fin (edgeCount G) =>
        colVerify Com (ℓ.eval n) G e (P'.next x [] (List.ofFn rP) [])
          (P'.next x [] (List.ofFn rP) [edgeMsg e]) = true
      simp only [id] at hbound
      have hev : ∀ rV : (colVerifier Com ℓ).Coins x.length,
          (colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))
            (P'.next x [] (List.ofFn (rP, rV).1) [])
            (P'.next x [] (List.ofFn (rP, rV).1)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))]) = true) ↔
          (colVerify Com (ℓ.eval n) G
            (sampleEdgeIdx (edgeCount G) x.length (List.ofFn fun i => rV (Fin.castLE hle i)))
            (P'.next x [] (List.ofFn rP) [])
            (P'.next x [] (List.ofFn rP)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length
                (List.ofFn fun i => rV (Fin.castLE hle i)))]) = true) := by
        intro rV
        rw [← ColProofs.sampleEdgeIdx_ofFn_castLE hle rV]
      refine (le_of_eq (OneWay.uprob_congr hev)).trans (hbound.trans ?_)
      have hcheat := uprob_check_uniform_le hC hn hnc (P'.next x [] (List.ofFn rP) [])
        fun e => P'.next x [] (List.ofFn rP) [edgeMsg e]
      have hinv : 1 / (x.length : ℝ) ≤ 1 / (edgeCount G : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmx)
      linarith
    · -- fewer than two vertices with an edge: the verifier rejects outright
      have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
        intro r
        rw [hout r]
        simp [hm.ne', hn]
      rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
      rw [uprob_false]
      exact hs0
  · have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
        ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
      intro r
      rw [hout r]
      simp [hwf]
    rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
    rw [uprob_false]
    exact hs0

end OneIteration


/-- `R_3COL` is a witness relation for `3COL` [PS10, Definition 191.11 for Theorem 124.1]:
witnesses have length `2n ≤ 2|x|`, and the relation is decided in polynomial time by
re-encoding the decoded graph and colouring and checking every edge.

**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))`, correct by `decGraph_encGraph` and
`decColoring_encColoring`, and polynomial-time by `polyTimeComputable_pairEq` on the
re-encodings (`polyTimeComputable_blockMap`, `polyTimeComputable_iterateEmit`) and a scan of
the `n²` entries for the colouring test (`polyTimeComputable_iterate` with an accumulated
conjunction). -/
theorem R3COL_witnessRelation : WitnessRelation L3COL R3COL := by
  refine ⟨mem_L3COL_iff, ⟨.mul (.const 2) .var, ?_⟩, ?_⟩
  · rintro x y ⟨n, G, c, rfl, rfl, -⟩
    rw [length_encColoring, length_encGraph, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_var]
    nlinarith [Nat.zero_le n]
  · sorry

/-- **One iteration of [PS10, Protocol 127.5] is an interactive proof for `3COL` with
efficient prover and soundness error `1 - 1/|x| + (1/2)^{|x|}`** [PS10, Proposition 127.6,
one iteration: "a cheating prover is caught with probability `1/|E|`"] (Prop-127.6,
Claim-127.e, Claim-127.h).

**Deviation (D10):** the error `1 - 1/|E|` is stated through `|E| ≤ |x|`, plus the edge
sampler's failure term `(1/2)^{|x|}`; here `|E| = edgeCount G ≤ n² = |x|` counts ordered
pairs (run-3 audit P11-3), which is what makes `|E| ≤ |x|` immediate.

**Proof sketch.** Completeness for every witness: for `x = encGraph G`, `y = encColoring c`
with `c` proper, the transcript is `[com, opn]` with `com = colCommit (π ∘ c) r` and
`opn = colOpen (π ∘ c) r p` for `p = edgeAt G e` (`exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, `edgeIdxOfMsg_edgeMsg` with `sampleEdgeIdx_lt`), and the verdict is
`[true]` by `colWellFormed_encGraph`, `colVerify_honest` when `E ≠ ∅` (then `n ≥ 2`: a graph
with an edge and a proper colouring has two distinct vertices) and outright when `E = ∅`, for
every value of `π` and `e` (`HardcoreBit.uprob_eq_one_of_forall`). Completeness of
`InteractiveProofErr` is the witness of `mem_L3COL_iff`. Soundness: for `x ∉ 3COL` either
`colWellFormed x = false` (verdict `[false]` always) or `x = encGraph G` with `¬ ThreeColorable G`
(`encGraph_mem_L3COL_iff`), so `0 < |E|` (`edgeCount_pos_of_not_threeColorable`); if `n < 2`
the verdict is `[false]`; otherwise fix the prover's coins (`Protocol.exists_proverCoins_le`),
replace the sampled edge by a uniform one (`statClose_sampleEdgeIdx`,
`StatClose.abs_uprob_sub_le_prod`, cost `(1/2)^{|x|}`), and apply `uprob_col_cheat_le` with
`k = 1`, `comF :=` the prover's first message and `opnF :=` its reply to `1^e`, giving
`Pr[accept] ≤ 1 - 1/|E| + (1/2)^{|x|} ≤ 1 - 1/|x| + (1/2)^{|x|}` (`|E| ≤ n² = |x|`), i.e. the
`[false]` probability is at least `1 - s |x|` (`uprob_not`). Efficiency:
`colProver_efficient`, `colVerifier_efficient` from `hC.easy`. -/
theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
      (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) where
  efficientV := colVerifier_efficient hC.easy ℓ
  complete := by
    intro x hx
    obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
    exact ⟨encColoring c, fun z => HardcoreBit.uprob_eq_one_of_forall fun r =>
      colProtocol_outV_honest hc z r⟩
  sound := fun x hx P' z => colProtocol_sound hC x hx P' z
  efficientP := colProver_efficient hC.easy ℓ
  completeWitness := by
    rintro x y ⟨n, G, c, rfl, rfl, hc⟩ z
    exact HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r

/-- **The `n|E|`-fold [PS10, Protocol 127.5] is an interactive proof for `3COL` with efficient
prover** [PS10, Proposition 127.6, "the probability of successfully cheating in all rounds is
`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Prop-127.6, Claim-127.h, Claim-125.a).

**Deviation:** `n|E|` iterations inside `4|x|²` fixed moves (D8); the soundness error carries the
edge samplers' failure term `|x|² (1/2)^{|x|}` (D10); the text's "`|E|²` times" is the
protocol's `n|E|`.

**Proof sketch.** Completeness as in `col_efficientProverProofErr`, iteration by iteration
(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`; the empty
messages beyond `n|E|` iterations are ignored). Soundness with
`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): for `x = encGraph G`
not colourable with `n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers
being uniform (`statClose_sampleEdgeIdx` per block, `StatClose.prod` iterated,
`StatClose.abs_uprob_sub_le_prod`, union cost `n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply
`uprob_col_cheat_le` with `k = n|E|`, `comF i` the prover's commitment of iteration `i` (a
function of the earlier challenges through `exec`) and `opnF i` its opening: the acceptance
probability is at most `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`) with
`n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`). Negligibility:
`negligible_exp_neg_sqrt_div` with `C = 1`, `Negligible.mul_pow negligible_two_pow_neg 2`,
`negligible_two_pow_neg`, `Negligible.add`. Efficiency: `colProverRep_efficient`,
`colVerifierRep_efficient`. -/
theorem colRep_efficientProverProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL := by
  sorry

/-- The `n|E|`-fold protocol is an interactive proof for `3COL` [PS10, Proposition 127.6]. -/
theorem colRep_interactiveProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : InteractiveProof (colProtocolRep Com ℓ) L3COL :=
  (colRep_efficientProverProof hC).toInteractiveProof

end TCSlib.Cryptography
