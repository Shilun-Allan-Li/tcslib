/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: completeness and soundness of the single iterations

[PS10, Proposition 118.4] (one iteration of the graph non-isomorphism protocol, soundness
error `1/2 + n·2^{-n}`) and [PS10, Proposition 120.7] (one iteration of the graph isomorphism
protocol, soundness error `1/2`, efficient prover), proved for the shadow protocols of
`GraphIsomorphism/Proofs.lean`; the main file `ZeroKnowledge/GraphIsomorphism.lean` closes
`gni_interactiveProofErr` and `gi_efficientProverProofErr` by `exact GI.…` (the efficiency
clauses are passed in as hypotheses, so that this file does not depend on the machine
constructions of `GraphIsomorphism/Efficiency.lean`).

**Completeness** is exact (`uprob = 1`): on an encoded instance the honest verdict is `[true]`
for every pair of random tapes (`gni_honest_reply`, `gi_honest_reply_eq`), whatever the
rejection-sampled permutation. **Soundness** of the graph non-isomorphism iteration is the
statistical argument of the text: against isomorphic graphs the relabelled graph `σ(G_b)` is
independent of `b` (`uprob_guess_eq_half`), and the honest verifier's `σ` is within
`permFailBound n` of uniform on its tape (`statClose_samplePerm_long`), whence
`Pr[accept] ≤ 1/2 + permFailBound n` after fixing the prover's coins
(`Protocol.exists_proverCoins_le`). Soundness of the graph isomorphism iteration is
`uprob_gi_cheat_le_half` (Lem-120.c): a prover can answer at most one of the two challenges.
Malformed common inputs are rejected outright by the well-formedness test.

## Main definitions

* `TCSlib.Cryptography.GI.vTapeSplit`, `GI.giBitEquiv`, `GI.giCoinEquiv` — the verifiers' random
  tapes as (challenge bit, sampler coins) and the joint coins as (bit, prover's coins).

## Main results

* `TCSlib.Cryptography.GI.gni_complete`, `GI.gni_accept_le` — completeness and the acceptance
  bound of one iteration of the graph non-isomorphism protocol.
* `TCSlib.Cryptography.GI.gi_complete`, `GI.gi_accept_le` — the same for the graph isomorphism
  protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErr` — [PS10, Proposition 118.4], one iteration.
* `TCSlib.Cryptography.GI.gi_efficientProverProofErr` — [PS10, Proposition 120.7], one iteration.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Verdicts of the graph non-isomorphism iteration on encoded instances -/

/-- The honest prover's reply to the graph `encGraph K` on an encoded instance:
`decide (¬ G₀ ≅ K)`. -/
theorem gniProver_next_encGraph {n : ℕ} (G₀ G₁ K : Graph n) (y r : List Bool) :
    gniProver.next (encInstance G₀ G₁) y r [encGraph K] = [decide (¬ Isomorphic G₀ K)] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (encGraph K)))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph, decGraphAt_encGraph]

/-- The verdict of the graph non-isomorphism iteration against a prover `P'` on an encoded
instance: the reply's first bit equals the verifier's first coin `b`, the graph sent being
`σ(G_b)` for `σ` sampled from the remaining coins. -/
theorem gni_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide ((P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
        [encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r.2).drop 1)))]).headD false = (List.ofFn r.2).headD false)] := by
  rw [gniProtocol_outV, gniVerifier_next_nil, gniVerifier_next_one, wellFormedInstance_encInstance]
  simp only [true_and]

/-- **Completeness of the graph non-isomorphism iteration** [PS10, Proposition 118.4]
(Lem-119.d): on a non-isomorphic encoded instance the honest prover's reply is the verifier's
bit for every pair of tapes (`gni_honest_reply`), so the verdict is `[true]` with probability
one. -/
theorem gni_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocol.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gni_outV_eq, gniProver_next_encGraph]
  simp only [List.headD_cons, gni_honest_reply h, decide_true]

/-- The verifier's tape of the graph non-isomorphism iteration as its first bit and the
sampler's `(N + 1)²` coins (`tapeSplit`, at the verifier's coin polynomial
`1 + (N + 1)²`). -/
def vTapeSplit (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ gniProtocol.V.Coins N :=
  tapeSplit (1 * (N + 1) ^ 2)

/-- The list of a split verifier tape. -/
theorem ofFn_vTapeSplit (N : ℕ) (b : Bool) (t : Fin (1 * (N + 1) ^ 2) → Bool) :
    List.ofFn (vTapeSplit N (b, t)) = b :: List.ofFn t :=
  ofFn_tapeSplit _ b t

/-- The sampler's coins fit in the verifier's tape: `permCoinLen n ≤ (|x| + 1)²` for an
encoded instance `x` on `n` vertices (`permCoinLen_le`, `length_encInstance`). -/
theorem permCoinLen_le_tape {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 := by
  rw [one_mul]
  exact permCoinLen_le (by rw [length_encInstance]; omega)

/-- **The acceptance bound of the graph non-isomorphism iteration against isomorphic graphs**
[PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the verifier
accepts with probability at most `1/2 + permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); the prover's reply
is then a function `g` of the graph it receives. Split the verifier's tape into the bit `b`
and the sampler's coins (`vTapeSplit`); the event is `g (σ(G_b)) = b` with `σ` the sampled
permutation. Replacing `σ` by a uniform permutation changes the probability by at most
`permFailBound n` (`statClose_samplePerm_long`, `StatClose.abs_uprob_sub_le_prod` with `b` as
the auxiliary coin), and for a uniform `σ` the probability is exactly `1/2`
(`uprob_guess_eq_half`). -/
theorem gni_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 + permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocol.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  set g : Graph n → Bool := fun K =>
    (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [encGraph K]).headD false with hg
  have hev : ∀ r₂ : gniProtocol.V.Coins (encInstance G₀ G₁).length,
      gniProtocol.outV P' (encInstance G₀ G₁) y z (r₁, r₂) = [true] ↔
        g (permGraph (cond ((List.ofFn r₂).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r₂).drop 1))) = (List.ofFn r₂).headD false := by
    intro r₂
    rw [gni_outV_eq]
    simp [hg]
  rw [OneWay.uprob_congr hev, ← uprob_comp_equiv (vTapeSplit (encInstance G₀ G₁).length)]
  have hev2 : ∀ p : Bool × (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool),
      g (permGraph (cond ((List.ofFn (vTapeSplit _ p)).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn (vTapeSplit _ p)).drop 1))) =
            (List.ofFn (vTapeSplit _ p)).headD false ↔
        g (permGraph (cond p.1 G₁ G₀) (samplePerm n (List.ofFn p.2))) = p.1 := by
    rintro ⟨b, t⟩
    rw [ofFn_vTapeSplit, List.headD_cons, List.drop_one, List.tail_cons]
  rw [OneWay.uprob_congr hev2,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool) Bool)]
  have hclose := (statClose_samplePerm_long (permCoinLen_le_tape G₀ G₁)).abs_uprob_sub_le_prod
    fun σ b => g (permGraph (cond b G₁ G₀) σ) = b
  have hideal : uprob (fun q : Equiv.Perm (Fin n) × Bool =>
      g (permGraph (cond q.2 G₁ G₀) (id q.1)) = q.2) = 1 / 2 := by
    rw [← uprob_comp_equiv (Equiv.prodComm Bool (Equiv.Perm (Fin n)))]
    exact uprob_guess_eq_half hσ g
  rw [hideal] at hclose
  have := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  linarith

/-- **One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n`** [PS10, Proposition 118.4, one
iteration] (Prop-118.4), given the verifier's efficiency.

**Proof sketch.** Completeness: `gni_complete` with the empty auxiliary input. Soundness: a
malformed `x` is rejected outright (`gniVerifier_next_one`); a well-formed `x ∉ L_niso` is
`encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gni_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gni_outV_eq`, `uprob_not`). -/
theorem gni_interactiveProofErr (hV : gniVerifier.Efficient) :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], fun z => gni_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gni_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocol.ExecCoins P' (encInstance G₀ G₁),
          gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gni_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocol.ExecCoins P' x, gniProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocol_outV, gniVerifier_next_one]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      linarith [permFailBound_nonneg (instanceVertices x.length)]

/-! ### Verdicts of the graph isomorphism iteration on encoded instances -/

/-- The verdict of the graph isomorphism iteration against a prover `P'` on an encoded
instance: `γ(G_b) = H` for the prover's two messages `H` (on the empty history) and `γ` (on
the challenge `[b]`). -/
theorem gi_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : giProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    giProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide (encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
        (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [[(List.ofFn r.2).headD false]]))) =
        P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])] := by
  rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two]

/-- **Completeness of the graph isomorphism iteration for every witness**
[PS10, Proposition 120.7] (Lem-120.a): with witness `encPerm σ`, `σ(G₀) = G₁`, the honest
transcript is `H = π(G₀)`, `γ = if b then π σ⁻¹ else π`, and `γ(G_b) = H` for every pair of
tapes (`gi_honest_reply_eq`), whatever the sampled `π`. -/
theorem gi_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins giProver (encInstance G₀ G₁) =>
      giProtocol.outV giProver (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gi_outV_eq, giProver_next_nil, giProver_next_cons, decPerm_encPerm, List.headD_cons,
    gi_honest_reply_eq hσ]
  simp

/-- The single coin of the graph isomorphism verifier as a tape (`Equiv.funUnique`). -/
def giBitEquiv (N : ℕ) : Bool ≃ giProtocol.V.Coins N := (Equiv.funUnique (Fin 1) Bool).symm

/-- The list of the verifier's single-coin tape. -/
theorem ofFn_giBitEquiv (N : ℕ) (b : Bool) : List.ofFn (giBitEquiv N b) = [b] := by
  show List.ofFn (fun _ : Fin 1 => b) = [b]
  rw [List.ofFn_succ, List.ofFn_zero]

/-- The joint coins of the graph isomorphism iteration as (challenge bit, prover's coins). -/
def giCoinEquiv (P' : Strategy) (x : List Bool) :
    Bool × P'.Coins x.length ≃ giProtocol.ExecCoins P' x :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (giBitEquiv x.length))

/-- The prover's coins of a transported pair. -/
theorem giCoinEquiv_fst (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).1 = r₁ := rfl

/-- The verifier's tape of a transported pair. -/
theorem giCoinEquiv_snd (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).2 = giBitEquiv x.length b := rfl

/-- **The acceptance bound of the graph isomorphism iteration against non-isomorphic graphs**
[PS10, proof of Proposition 120.7] (Lem-120.c): for `G₀ ≇ G₁` and every prover `P'`, the
verifier accepts with probability at most `1/2`.

**Proof sketch.** Acceptance means `γ(G_b) = H` for the decoded first message `H` and decoded
reply `γ` (`gi_outV_eq`, `decGraphAt_encGraph`); the event is contained in the event of
`uprob_gi_cheat_le_half` with `H r₁ := decGraphAt n (first message)` and
`γ b r₁ := decPerm n (reply to [b])`, after reading the joint coins as (bit, prover's coins)
(`giCoinEquiv`). -/
theorem gi_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 := by
  set H : P'.Coins (encInstance G₀ G₁).length → Graph n := fun r₁ =>
    decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) []) with hH
  set γ : Bool → P'.Coins (encInstance G₀ G₁).length → Equiv.Perm (Fin n) := fun b r₁ =>
    decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [[b]]) with hγ
  have hmono : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true] →
        permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀) (γ ((List.ofFn r.2).headD false) r.1) =
          H r.1 := by
    intro r hr
    rw [gi_outV_eq] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    show permGraph _ (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
      [[(List.ofFn r.2).headD false]])) = decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])
    rw [← hr, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giCoinEquiv P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_) (uprob_gi_cheat_le_half h H γ)
  rintro ⟨b, r₁⟩
  rw [giCoinEquiv_fst, giCoinEquiv_snd, ofFn_giBitEquiv, List.headD_cons]

/-- **One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, corrected: for `L_iso`] (Prop-120.7), given the parties'
efficiency.

**Proof sketch.** Completeness for every witness: `gi_complete`; completeness of
`InteractiveProofErr`: the witness `encPerm σ`. Soundness: a malformed `x` is rejected
outright (`giVerifier_next_two'`); a well-formed `x ∉ L_iso` is `encInstance G₀ G₁` with
`G₀ ≇ G₁` (`eq_encInstance_of_wellFormed`, `encInstance_mem_Liso_iff`) and `gi_accept_le`
bounds the acceptance probability, the verdict being a single bit (`gi_outV_eq`,
`uprob_not`). -/
theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Efficient) :
    EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) where
  efficientV := hV
  complete := by
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, fun z => gi_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := gi_accept_le hni P' [] z
      have hnot : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
          giProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gi_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocol.ExecCoins P' x, giProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two']
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      norm_num
  efficientP := hP
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact gi_complete hσ z

end TCSlib.Cryptography.GI
