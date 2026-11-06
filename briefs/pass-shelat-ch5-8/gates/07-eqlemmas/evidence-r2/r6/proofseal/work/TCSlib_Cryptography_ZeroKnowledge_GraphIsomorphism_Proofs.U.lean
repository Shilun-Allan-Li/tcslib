/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Complexity.Randomized.Closure
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: shadow definitions and generic proof infrastructure

Proof infrastructure for `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism` ([PS10, §4.5],
Protocols 118.3 and 120.6). That file is at the file-size limit, so the proofs of its
theorems live in the sibling files `GraphIsomorphism/Proofs.lean` (this file),
`GraphIsomorphism/Efficiency.lean` and `GraphIsomorphism/Soundness.lean`, which the main
file imports. An imported file cannot refer to the main file's definitions, so this file
restates them **verbatim** in the inner namespace `TCSlib.Cryptography.GI` (the *shadow*
definitions): every shadow is definitionally equal to its original, and the main file closes
each of its targets by `exact GI.…`, which type-checks by `rfl`. The shadows are proof
devices, not public API; they must be kept in sync with the frozen definitions of the main
file (any divergence makes the main file's `exact` fail to type-check, so a divergence cannot
go unnoticed).

Besides the shadows, this file holds the generic infrastructure shared by the efficiency and
the soundness proofs: the decode/encode identities on a given vertex count, the
characterisation of well-formed instances, the transcripts of the single-iteration protocols,
the bit/tape bijections used to read a verifier's random tape as (challenge bit, sampler
coins), the fact that the permutation sampler reads only a prefix of its tape, and the
shadow copies of the concrete probability lemmas of the main file that the soundness proofs
need (Lem-119.a, Lem-120.b–c, the honest replies).

## Main definitions

* `TCSlib.Cryptography.GI.Isomorphic`, `GI.decGraphAt`, `GI.encInstance`,
  `GI.instanceVertexCount`, `GI.instanceG₀`, `GI.instanceG₁`, `GI.wellFormedInstance`,
  `GI.instanceVertices`, `GI.Liso`, `GI.Lniso`, `GI.Riso`, `GI.samplePerm`, `GI.permCoinLen`,
  `GI.permFailBound`, `GI.coinSlice` — shadows of the definitions of the main file.
* `TCSlib.Cryptography.GI.gniProver`, `GI.gniVerifier`, `GI.gniProtocol`, `GI.gniVerifierRep`,
  `GI.gniProtocolRep`, `GI.giProver`, `GI.giVerifier`, `GI.giProtocol`, `GI.giProverRep`,
  `GI.giVerifierRep`, `GI.giProtocolRep` — shadows of the strategies and protocols.
* `TCSlib.Cryptography.GI.tapeSplit` — a tape of `1 + c` bits as a bit and a tape of `c` bits.

## Main results

* `TCSlib.Cryptography.GI.encGraph_decGraphAt`, `GI.eq_encInstance_of_wellFormed` — a word of
  length `n²` is the encoding of its decoding; a well-formed instance is `encInstance` of its
  two graphs.
* `TCSlib.Cryptography.GI.efficient_of_polyTime` — a strategy whose next-message function is a
  polynomial-time function of the machine layout is efficient.
* `TCSlib.Cryptography.GI.giProver_length_le`, `GI.giProverRep_length_le`,
  `GI.gniProver_length_le` — the honest provers' messages have at most `|x|` bits (one bit for
  graph non-isomorphism), whatever the tape and history (ruling G3-3).
* `TCSlib.Cryptography.GI.gniProtocol_outV`, `GI.giProtocol_outV` and the `*_next_*` lemmas —
  the verdicts of the single-iteration protocols on encoded instances.
* `TCSlib.Cryptography.GI.pushesUniform_castLE`, `GI.statClose_samplePerm_long` — a prefix of a
  uniform tape is uniform, so the sampler is close to uniform on any tape long enough.
* `TCSlib.Cryptography.GI.uprob_guess_eq_half` — against isomorphic graphs the relabelled
  graph is independent of the challenge bit: any guess is right with probability exactly `1/2`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Shadow definitions (verbatim copies of `GraphIsomorphism.lean`) -/

/-- Shadow of `TCSlib.Cryptography.Isomorphic` (Def-117.e). -/
def Isomorphic {n : ℕ} (G₀ G₁ : Graph n) : Prop := ∃ σ : Equiv.Perm (Fin n), permGraph G₀ σ = G₁

/-- Shadow of the decidability instance of `Isomorphic`. -/
instance {n : ℕ} (G₀ G₁ : Graph n) : Decidable (Isomorphic G₀ G₁) := by
  unfold Isomorphic
  infer_instance

/-- Shadow of `TCSlib.Cryptography.decGraphAt`. -/
def decGraphAt (n : ℕ) (w : List Bool) : Graph n := fun u v => w.getD (finProdFinEquiv (u, v)) false

/-- Shadow of `TCSlib.Cryptography.encInstance`. -/
def encInstance {n : ℕ} (G₀ G₁ : Graph n) : List Bool := pairEncode (encGraph G₀) (encGraph G₁)

/-- Shadow of `TCSlib.Cryptography.instanceVertexCount`. -/
def instanceVertexCount (x : List Bool) : ℕ := Nat.sqrt (pairFstD x).length

/-- Shadow of `TCSlib.Cryptography.instanceG₀`. -/
def instanceG₀ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairFstD x)

/-- Shadow of `TCSlib.Cryptography.instanceG₁`. -/
def instanceG₁ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairSndD x)

/-- Shadow of `TCSlib.Cryptography.wellFormedInstance`. -/
def wellFormedInstance (x : List Bool) : Bool :=
  decide ((pairDecode x).isSome ∧ (pairFstD x).length = instanceVertexCount x * instanceVertexCount x ∧
    (pairSndD x).length = instanceVertexCount x * instanceVertexCount x)

/-- Shadow of `TCSlib.Cryptography.instanceVertices`. -/
def instanceVertices (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 3)

/-- Shadow of `TCSlib.Cryptography.Liso` (Def-118.a). -/
def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

/-- Shadow of `TCSlib.Cryptography.Lniso` (Def-118.a). -/
def Lniso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n), x = pairEncode (encGraph G₀) (encGraph G₁) ∧ ¬ Isomorphic G₀ G₁}

/-- Shadow of `TCSlib.Cryptography.Riso` (Def-118.a). -/
def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

/-- Shadow of `TCSlib.Cryptography.samplePerm` (D10). -/
noncomputable def samplePerm (n : ℕ) (r : List Bool) : Equiv.Perm (Fin n) :=
  (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1

/-- Shadow of `TCSlib.Cryptography.permCoinLen`. -/
def permCoinLen (n : ℕ) : ℕ := n * permTrials n * permBits n

/-- Shadow of `TCSlib.Cryptography.permFailBound`. -/
noncomputable def permFailBound (n : ℕ) : ℝ := n * (2 : ℝ)⁻¹ ^ n

/-- Shadow of `TCSlib.Cryptography.coinSlice`. -/
def coinSlice (c i : ℕ) (r : List Bool) : List Bool := (r.drop (i * c)).take c

/-- Shadow of `TCSlib.Cryptography.gniProver` [PS10, Protocol 118.3]. -/
def gniProver : Strategy where
  coins := .const 0
  next x _ _ hist :=
    [decide (¬ Isomorphic (instanceG₀ x) (decGraphAt (instanceVertexCount x) (hist.getLastD [])))]

/-- Shadow of `TCSlib.Cryptography.gniVerifier` [PS10, Protocol 118.3]. -/
noncomputable def gniVerifier : Strategy where
  coins := .add (.const 1) (.normal 1 2)
  next x _ r hist :=
    let b := r.headD false
    match hist with
    | [] => encGraph (permGraph (if b then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (r.drop 1)))
    | [b'] => [decide (wellFormedInstance x = true ∧ b'.headD false = b)]
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.gniProtocol` (Prot-118.3). -/
noncomputable def gniProtocol : Protocol where
  P := gniProver
  V := gniVerifier
  rounds := .const 2
  verifierFirst := true

/-- Shadow of `TCSlib.Cryptography.gniVerifierRep`. -/
noncomputable def gniVerifierRep : Strategy where
  coins := .mul .var (.add (.const 1) (.normal 1 2))
  next x _ r hist :=
    let c := 1 + (x.length + 1) ^ 2
    if hist.length < x.length then
      let ri := coinSlice c hist.length r
      encGraph (permGraph (if ri.headD false then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (ri.drop 1)))
    else
      [decide (wellFormedInstance x = true ∧
        ∀ j : Fin x.length, (hist.getD j []).headD false = (coinSlice c j r).headD false)]

/-- Shadow of `TCSlib.Cryptography.gniProtocolRep` (Prot-118.3). -/
noncomputable def gniProtocolRep : Protocol where
  P := gniProver
  V := gniVerifierRep
  rounds := .mul (.const 2) .var
  verifierFirst := true

/-- Shadow of `TCSlib.Cryptography.giProver` [PS10, Protocol 120.6]. -/
noncomputable def giProver : Strategy where
  coins := .normal 1 2
  next x y r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let σ := decPerm n y
    let π := samplePerm n r
    match hist with
    | [] => encGraph (permGraph G₀ π)
    | _ :: _ => encPerm (if (hist.headD []).headD false then π * σ⁻¹ else π)

/-- Shadow of `TCSlib.Cryptography.giVerifier` [PS10, Protocol 120.6]. -/
noncomputable def giVerifier : Strategy where
  coins := .const 1
  next x _ r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let G₁ : Graph n := fun u v => (pairSndD x).getD (finProdFinEquiv (u, v)) false
    let b := r.headD false
    match hist with
    | [H, γ] => [decide (wellFormedInstance x = true ∧
        encGraph (permGraph (if b then G₁ else G₀) (decPerm n γ)) = H)]
    | [_] => [b]
    | _ => [false]

/-- Shadow of `TCSlib.Cryptography.giProtocol` (Prot-120.6). -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

/-- Shadow of `TCSlib.Cryptography.giProverRep`. -/
noncomputable def giProverRep : Strategy where
  coins := .mul .var (.normal 1 2)
  next x y r hist :=
    let n := instanceVertexCount x
    let σ := decPerm n y
    let π := samplePerm n (coinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)
    if hist.length % 2 = 0 then encGraph (permGraph (instanceG₀ x) π)
    else encPerm (if (hist.getLastD []).headD false then π * σ⁻¹ else π)

/-- Shadow of `TCSlib.Cryptography.giVerifierRep`. -/
noncomputable def giVerifierRep : Strategy where
  coins := .var
  next x _ r hist :=
    let n := instanceVertexCount x
    if hist.length % 2 = 1 then [r.getD (hist.length / 2) false]
    else if hist.length < 2 * x.length then []
    else [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
      encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm n (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])]

/-- Shadow of `TCSlib.Cryptography.giProtocolRep` (Prot-120.6). -/
noncomputable def giProtocolRep : Protocol where
  P := giProverRep
  V := giVerifierRep
  rounds := .mul (.const 4) .var
  verifierFirst := false

/-! ### Bounded prover messages (ruling G3-3 of gate 03) -/

/-- The honest prover of one graph-isomorphism iteration sends `n²`-bit words (`encGraph`,
`encPerm`) with `n = Nat.sqrt` of the length of the first component of `x`, hence at most
`|x|` bits, whatever its auxiliary input, tape and history (`Nat.sqrt_le`,
`length_pairFstD_le`). -/
theorem giProver_length_le (x y r : List Bool) (hist : List (List Bool)) :
    (giProver.next x y r hist).length ≤ x.length := by
  have h : (giProver.next x y r hist).length =
      Nat.sqrt (pairFstD x).length * Nat.sqrt (pairFstD x).length := by
    cases hist <;> simp [giProver, decGraph]
  rw [h]
  exact (Nat.sqrt_le _).trans (length_pairFstD_le x)

/-- The honest prover of the `|x|`-fold graph-isomorphism protocol sends at most `|x|` bits per
message, as in one iteration (`giProver_length_le`). -/
theorem giProverRep_length_le (x y r : List Bool) (hist : List (List Bool)) :
    (giProverRep.next x y r hist).length ≤ x.length := by
  have h : (giProverRep.next x y r hist).length =
      Nat.sqrt (pairFstD x).length * Nat.sqrt (pairFstD x).length := by
    simp only [giProverRep]
    split_ifs <;> simp [instanceVertexCount]
  rw [h]
  exact (Nat.sqrt_le _).trans (length_pairFstD_le x)

/-- The honest prover of the graph non-isomorphism protocol sends one bit per message. -/
theorem gniProver_length_le (x y r : List Bool) (hist : List (List Bool)) :
    (gniProver.next x y r hist).length ≤ 1 := by
  simp [gniProver]

/-! ### Isomorphism algebra (shadow copies of the main file's lemmas) -/

/-- Every graph is isomorphic to itself. -/
theorem Isomorphic.refl {n : ℕ} (G : Graph n) : Isomorphic G G := ⟨1, permGraph_one G⟩

/-- Isomorphism is symmetric. -/
theorem Isomorphic.symm {n : ℕ} {G₀ G₁ : Graph n} (h : Isomorphic G₀ G₁) : Isomorphic G₁ G₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, permGraph_permGraph_inv]⟩

/-- Isomorphism is transitive. -/
theorem Isomorphic.trans {n : ℕ} {G₀ G₁ G₂ : Graph n} (h₁ : Isomorphic G₀ G₁)
    (h₂ : Isomorphic G₁ G₂) : Isomorphic G₀ G₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [← permGraph_mul, hσ, hτ]⟩

/-- A graph is isomorphic to each of its relabellings. -/
theorem isomorphic_permGraph {n : ℕ} (G : Graph n) (σ : Equiv.Perm (Fin n)) :
    Isomorphic G (permGraph G σ) := ⟨σ, rfl⟩

/-- A graph is isomorphic to at most one of two non-isomorphic graphs (Lem-120.b). -/
theorem not_isomorphic_both {n : ℕ} {G₀ G₁ H : Graph n} (h : ¬ Isomorphic G₀ G₁) :
    ¬ (Isomorphic G₀ H ∧ Isomorphic G₁ H) := fun ⟨h₀, h₁⟩ => h (h₀.trans h₁.symm)

/-- The honest prover's reply of the graph isomorphism protocol is accepted (Lem-120.a). -/
theorem gi_honest_reply_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) (b : Bool) :
    permGraph (cond b G₁ G₀) (if b then π * σ⁻¹ else π) = permGraph G₀ π := by
  cases b
  · rfl
  · exact permGraph_mul_inv_of_eq hσ π

/-- The honest prover of the graph non-isomorphism protocol recovers the bit (Lem-119.d). -/
theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (b : Bool)
    (σ : Equiv.Perm (Fin n)) :
    decide (¬ Isomorphic G₀ (permGraph (cond b G₁ G₀) σ)) = b := by
  cases b
  · exact decide_eq_false (not_not.2 (isomorphic_permGraph G₀ σ))
  · exact decide_eq_true fun h' => h (h'.trans (isomorphic_permGraph G₁ σ).symm)

/-! ### Encoded instances -/

/-- Decoding an encoded graph on its own vertex count gives the graph back. -/
@[simp] theorem decGraphAt_encGraph {n : ℕ} (G : Graph n) : decGraphAt n (encGraph G) = G :=
  funext fun u => funext fun v => encGraph_getD G u v

/-- A word of length `n²` is the encoding of its decoding on `n` vertices. -/
theorem encGraph_decGraphAt {n : ℕ} {w : List Bool} (h : w.length = n * n) :
    encGraph (decGraphAt n w) = w := by
  apply List.ext_getElem
  · simp [h]
  · intro k hk hk'
    simp only [encGraph, List.getElem_ofFn, decGraphAt, Prod.mk.eta, Equiv.apply_symm_apply]
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]

/-- An encoded instance on `n` vertices has `3n² + 2` bits. -/
theorem length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : (encInstance G₀ G₁).length = 3 * (n * n) + 2 := by
  simp only [encInstance, length_pairEncode, length_encGraph]
  ring

/-- `instanceVertices` recovers `n` from the length of an encoded instance. -/
theorem instanceVertices_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertices (encInstance G₀ G₁).length = n := by
  rw [instanceVertices, length_encInstance, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.sqrt_eq]

/-- The vertex count decoded from an encoded instance is `n`. -/
theorem instanceVertexCount_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertexCount (encInstance G₀ G₁) = n := by
  simp [instanceVertexCount, encInstance, Nat.sqrt_eq]

/-- Encoded instances are well formed. -/
theorem wellFormedInstance_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    wellFormedInstance (encInstance G₀ G₁) = true := by
  simp [wellFormedInstance, encInstance, instanceVertexCount, Nat.sqrt_eq, pairDecode_pairEncode]

/-- A well-formed instance is the encoding of its two decoded graphs. -/
theorem eq_encInstance_of_wellFormed {x : List Bool} (h : wellFormedInstance x = true) :
    x = encInstance (instanceG₀ x) (instanceG₁ x) := by
  simp only [wellFormedInstance, decide_eq_true_eq] at h
  obtain ⟨hs, h0, h1⟩ := h
  obtain ⟨⟨a, b⟩, hab⟩ := Option.isSome_iff_exists.1 hs
  have hx := eq_pairEncode_of_pairDecode x a b hab
  rw [encInstance, instanceG₀, instanceG₁, encGraph_decGraphAt h0, encGraph_decGraphAt h1, hx,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- A well-formed instance is an encoded pair of graphs on a common vertex set. -/
theorem exists_eq_encInstance_of_wellFormed {x : List Bool} (h : wellFormedInstance x = true) :
    ∃ (n : ℕ) (G₀ G₁ : Graph n), x = encInstance G₀ G₁ :=
  ⟨_, _, _, eq_encInstance_of_wellFormed h⟩

/-- Equal encodings come from the same vertex count and the same graph. -/
theorem sigma_eq_of_encGraph_eq {n n' : ℕ} {G : Graph n} {G' : Graph n'}
    (h : encGraph G = encGraph G') : (⟨n, G⟩ : Σ m, Graph m) = ⟨n', G'⟩ := by
  rw [← decGraph_encGraph G, ← decGraph_encGraph G', h]

/-- An encoded instance is in `L_iso` exactly when its graphs are isomorphic. -/
theorem encInstance_mem_Liso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Liso ↔ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', σ, hx, hσ⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨n, G₀, G₁, σ, rfl, hσ⟩

/-- An encoded instance is in `L_niso` exactly when its graphs are not isomorphic. -/
theorem encInstance_mem_Lniso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Lniso ↔ ¬ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', hx, hni⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact hni
  · intro h
    exact ⟨n, G₀, G₁, rfl, h⟩

/-- `decGraph` of a word whose length has square root `n` is the pair `⟨n, decGraphAt n w⟩`. -/
theorem decGraph_eq_of_sqrt {w : List Bool} {n : ℕ} (h : Nat.sqrt w.length = n) :
    decGraph w = ⟨n, decGraphAt n w⟩ := by
  subst h
  rfl

/-- The decoding of the empty word is the identity permutation (the default row search
returns the row index). -/
theorem decPerm_nil (n : ℕ) : decPerm n [] = 1 := by
  unfold decPerm
  have hid : (fun i : Fin n =>
      (Fin.find (fun j : Fin n => ([] : List Bool).getD (finProdFinEquiv (i, j)) false = true)).getD i) =
      id := by
    funext i
    have hnone : Fin.find (fun j : Fin n => ([] : List Bool).getD (finProdFinEquiv (i, j)) false = true) =
        none :=
      Fin.find_eq_none_iff.2 fun j => by simp
    rw [hnone]
    rfl
  simp only [hid]
  rw [dif_pos Function.bijective_id]
  exact Equiv.ext fun _ => rfl

/-! ### Efficiency from a polynomial-time layout function -/

/-- The interactive machine layout of a strategy activation,
`⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` (`Strategy.ofNUPPT`, `NUPPT.runAtL`). -/
def ilayout (x z : List Bool) (hist : List (List Bool)) (r : List Bool) : List Bool :=
  NUPPT.layout (List.replicate x.length true)
    (pairEncode (pairEncode x z) (Strategy.encodeMsgs hist)) [] r

/-- A strategy whose next-message function is a polynomial-time function `F` of the machine
layout `ilayout x z hist r = ⟨⟨⟨1^{|x|}, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩` is efficient:
`NUPPT.ofPolyTimeUniform` of `F` with the strategy's coin polynomial is the uniform machine
computing it (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem efficient_of_polyTime (S : Strategy) {F : List Bool → List Bool} (hF : PolyTimeComputable F)
    (h : ∀ x z r hist, S.next x z r hist = F (ilayout x z hist r)) : S.Efficient :=
  ⟨NUPPT.ofPolyTimeUniform hF S.coins, NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => by
      rw [h, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-! ### Transcripts of the single-iteration protocols -/

/-- The verdict of the graph non-isomorphism protocol against a prover `P'`: the verifier's
reply to the single message `P'` sends after receiving `H`. -/
theorem gniProtocol_outV (P' : Strategy) (x y z : List Bool) (r : gniProtocol.ExecCoins P' x) :
    gniProtocol.outV P' x y z r =
      gniVerifier.next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [gniVerifier.next x z (List.ofFn r.2) []]] := by
  simp [Protocol.outV, Protocol.transcriptWith, gniProtocol, exec, moverIsV]

/-- The verdict of the graph isomorphism protocol against a prover `P'`: the verifier's output
on the two messages `H` and `γ` of `P'`, the second being its reply to the challenge. -/
theorem giProtocol_outV (P' : Strategy) (x y z : List Bool) (r : giProtocol.ExecCoins P' x) :
    giProtocol.outV P' x y z r =
      giVerifier.next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1) [giVerifier.next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := by
  simp [Protocol.outV, Protocol.transcriptWith, giProtocol, exec, moverIsV]

/-- The first message of the graph non-isomorphism verifier on an encoded instance:
`σ(G_b)` for the first coin `b` and `σ` sampled from the remaining coins. -/
theorem gniVerifier_next_nil {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) :
    gniVerifier.next (encInstance G₀ G₁) z r [] =
      encGraph (permGraph (cond (r.headD false) G₁ G₀) (samplePerm n (r.drop 1))) := by
  show encGraph (permGraph (if r.headD false then
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁)) else
      decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁)) (r.drop 1))) = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph]
  cases r.headD false <;> rfl

/-- The verdict of the graph non-isomorphism verifier on one reply. -/
theorem gniVerifier_next_one (x z r b' : List Bool) :
    gniVerifier.next x z r [b'] =
      [decide (wellFormedInstance x = true ∧ b'.headD false = r.headD false)] := rfl

/-- The challenge of the graph isomorphism verifier is its single coin. -/
theorem giVerifier_next_one (x z r H : List Bool) : giVerifier.next x z r [H] = [r.headD false] := rfl

/-- The verdict of the graph isomorphism verifier on an encoded instance:
`γ(G_b) = H` for the challenge `b`. -/
theorem giVerifier_next_two {n : ℕ} (G₀ G₁ : Graph n) (z r H γ : List Bool) :
    giVerifier.next (encInstance G₀ G₁) z r [H, γ] =
      [decide (encGraph (permGraph (cond (r.headD false) G₁ G₀) (decPerm n γ)) = H)] := by
  show [decide (wellFormedInstance (encInstance G₀ G₁) = true ∧
    encGraph (permGraph (if r.headD false then
      decGraphAt (decGraph (pairFstD (encInstance G₀ G₁))).1 (pairSndD (encInstance G₀ G₁)) else
      (decGraph (pairFstD (encInstance G₀ G₁))).2)
      (decPerm (decGraph (pairFstD (encInstance G₀ G₁))).1 γ)) = H)] = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _,
    decGraph_encGraph, wellFormedInstance_encInstance]
  simp only [decGraphAt_encGraph, true_and]
  cases r.headD false <;> rfl

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

/-! ### Unfolding the single-iteration strategies on arbitrary inputs -/

/-- The graph isomorphism prover's first message, unfolded. -/
theorem giProver_next_nil' (x y r : List Bool) :
    giProver.next x y r [] =
      encGraph (permGraph (decGraph (pairFstD x)).2 (samplePerm (decGraph (pairFstD x)).1 r)) := rfl

/-- The graph isomorphism prover's reply, unfolded. -/
theorem giProver_next_cons' (x y r m : List Bool) (h : List (List Bool)) :
    giProver.next x y r (m :: h) =
      encPerm (if m.headD false then
        samplePerm (decGraph (pairFstD x)).1 r * (decPerm (decGraph (pairFstD x)).1 y)⁻¹
      else samplePerm (decGraph (pairFstD x)).1 r) := rfl

/-- The graph isomorphism verifier's verdict, unfolded. -/
theorem giVerifier_next_two' (x z r H γ : List Bool) :
    giVerifier.next x z r [H, γ] =
      [decide (wellFormedInstance x = true ∧ encGraph (permGraph
        (if r.headD false then decGraphAt (decGraph (pairFstD x)).1 (pairSndD x)
          else (decGraph (pairFstD x)).2) (decPerm (decGraph (pairFstD x)).1 γ)) = H)] := rfl

/-- The graph isomorphism verifier on the empty history. -/
theorem giVerifier_next_nil' (x z r : List Bool) : giVerifier.next x z r [] = [false] := rfl

/-- The graph isomorphism verifier on three or more messages. -/
theorem giVerifier_next_long' (x z r H γ m : List Bool) (t : List (List Bool)) :
    giVerifier.next x z r (H :: γ :: m :: t) = [false] := rfl

/-- The graph non-isomorphism verifier's first message, unfolded. -/
theorem gniVerifier_next_nil' (x z r : List Bool) :
    gniVerifier.next x z r [] =
      encGraph (permGraph (if r.headD false then decGraphAt (instanceVertexCount x) (pairSndD x)
        else decGraphAt (instanceVertexCount x) (pairFstD x))
        (samplePerm (instanceVertexCount x) (r.drop 1))) := rfl

/-- The graph non-isomorphism verifier on two or more replies. -/
theorem gniVerifier_next_long' (x z r b' m : List Bool) (t : List (List Bool)) :
    gniVerifier.next x z r (b' :: m :: t) = [false] := rfl

/-! ### Tapes: the first bit and the rest; prefixes -/

/-- A tape of `1 + c` bits as its first bit and the remaining `c` bits (`Fin.consEquiv` after
the cast `c + 1 = 1 + c`). -/
def tapeSplit (c : ℕ) : Bool × (Fin c → Bool) ≃ (Fin (1 + c) → Bool) :=
  (Fin.consEquiv fun _ => Bool).trans (Equiv.arrowCongr (finCongr (Nat.add_comm c 1)) (Equiv.refl Bool))

/-- The list of a split tape is the bit followed by the list of the rest. -/
theorem ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    List.ofFn (tapeSplit c (b, t)) = b :: List.ofFn t := by
  rw [List.ofFn_congr (Nat.add_comm 1 c), List.ofFn_succ]
  rfl

/-- The verifier's tape length of one graph non-isomorphism iteration: `1 + (N + 1)²`. -/
theorem gniProtocol_V_coinLen (N : ℕ) : gniProtocol.V.coinLen N = 1 + 1 * (N + 1) ^ 2 := by
  rw [Strategy.coinLen_eq]
  show (PolyExpr.add (.const 1) (.normal 1 2)).eval N = _
  rw [PolyExpr.eval_add, PolyExpr.eval_const, PolyExpr.eval_normal]

/-- The verifier's tape length of the `N`-fold graph non-isomorphism protocol:
`N · (1 + (N + 1)²)`. -/
theorem gniProtocolRep_V_coinLen (N : ℕ) :
    gniProtocolRep.V.coinLen N = N * (1 + 1 * (N + 1) ^ 2) := by
  rw [Strategy.coinLen_eq]
  show (PolyExpr.mul .var (.add (.const 1) (.normal 1 2))).eval N = _
  rw [PolyExpr.eval_mul, PolyExpr.eval_var, PolyExpr.eval_add, PolyExpr.eval_const,
    PolyExpr.eval_normal]

/-- The verifier's tape length of one graph isomorphism iteration: one bit. -/
theorem giProtocol_V_coinLen (N : ℕ) : giProtocol.V.coinLen N = 1 := by
  rw [Strategy.coinLen_eq]
  show (PolyExpr.const 1).eval N = _
  rw [PolyExpr.eval_const]

/-- The verifier's tape length of the `N`-fold graph isomorphism protocol: `N` bits. -/
theorem giProtocolRep_V_coinLen (N : ℕ) : giProtocolRep.V.coinLen N = N := by
  rw [Strategy.coinLen_eq]
  show PolyExpr.var.eval N = _
  rw [PolyExpr.eval_var]

/-- The first bit of a split tape. -/
theorem headD_ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    (List.ofFn (tapeSplit c (b, t))).headD false = b := by
  rw [ofFn_tapeSplit, List.headD_cons]

/-- The rest of a split tape. -/
theorem drop_ofFn_tapeSplit (c : ℕ) (b : Bool) (t : Fin c → Bool) :
    (List.ofFn (tapeSplit c (b, t))).drop 1 = List.ofFn t := by
  rw [ofFn_tapeSplit, List.drop_one, List.tail_cons]

/-- Restricting a uniform tape of `c` bits to its first `m ≤ c` bits gives a uniform tape:
the tape is the pair (prefix, suffix) through `finSumFinEquiv`, and the first projection pushes
uniform to uniform. -/
theorem pushesUniform_castLE {m c : ℕ} (h : m ≤ c) :
    HardcoreBit.PushesUniform (fun t : Fin c → Bool => fun i : Fin m => t (Fin.castLE h i)) := by
  let e : (Fin c → Bool) ≃ (Fin m → Bool) × (Fin (c - m) → Bool) :=
    (Equiv.arrowCongr (finCongr (Nat.add_sub_cancel' h).symm) (Equiv.refl Bool)).trans
      ((Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
        (Equiv.sumArrowEquivProdArrow _ _ _))
  have he : ∀ t : Fin c → Bool, (e t).1 = fun i : Fin m => t (Fin.castLE h i) := by
    intro t
    funext i
    simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
      Equiv.coe_refl, Function.comp_apply, Equiv.symm_symm, finCongr_symm,
      finCongr_apply, finSumFinEquiv_apply_left]
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

/-- Shadow of `statClose_samplePerm`: the sampler is within `permFailBound n` of uniform. -/
theorem statClose_samplePerm (n : ℕ) :
    StatClose (fun r : Fin (permCoinLen n) → Bool => samplePerm n (List.ofFn r))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) :=
  (statClose_permFromCoins_two_pow n 1).comp_pushesUniform
    (pushesUniform_coinTable n (permTrials n) (permBits n))

/-- On any tape of at least `permCoinLen n` bits the sampler is within `permFailBound n` of a
uniform permutation (`samplePerm_ofFn_castLE`, `pushesUniform_castLE`). -/
theorem statClose_samplePerm_long {n c : ℕ} (h : permCoinLen n ≤ c) :
    StatClose (fun t : Fin c → Bool => samplePerm n (List.ofFn t))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) := by
  have := (statClose_samplePerm n).comp_pushesUniform (pushesUniform_castLE h)
  intro T
  have hT := this T
  simpa only [samplePerm_ofFn_castLE h] using hT

/-- Shadow of `permCoinLen_le`: the sampler fits in `(N + 1)²` bits once `2n² ≤ N`. -/
theorem permCoinLen_le {n N : ℕ} (h : 2 * (n * n) ≤ N) : permCoinLen n ≤ (N + 1) ^ 2 := by
  have hnn : n * n ≤ N := le_trans (Nat.le_mul_of_pos_left (n * n) two_pos) h
  calc permCoinLen n = n * (2 * n * n) * permBits n := rfl
    _ ≤ n * (2 * n * n) * n := Nat.mul_le_mul_left _ (permBits_le n)
    _ = (2 * (n * n)) * (n * n) := by ring
    _ ≤ N * N := Nat.mul_le_mul h hnn
    _ ≤ (N + 1) ^ 2 := by nlinarith

/-- The failure bound is nonnegative. -/
theorem permFailBound_nonneg (n : ℕ) : 0 ≤ permFailBound n := by
  unfold permFailBound
  positivity

/-! ### Concrete probability lemmas (shadow copies) -/

/-- Shadow of `uprob_permGraph_eq_of_isomorphic'` (Lem-119.a): `σ(G₁)` and `σ(G₀)` have the
same law when `G₀ ≅ G₁`. -/
theorem uprob_permGraph_eq_of_isomorphic' {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → Prop) :
    uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₁ σ)) =
      uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ)) := by
  rw [← uprob_comp_equiv (Equiv.mulRight σ₀) (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ))]
  congr 1
  funext σ
  simp [← hσ, permGraph_mul]

/-- Against isomorphic graphs the relabelled graph `σ(G_b)` is independent of the bit `b`, so
any guess `g` of `b` from `σ(G_b)` is right with probability exactly `1/2` [PS10, proof of
Proposition 118.4, "`H` is independent of `b`"]. -/
theorem uprob_guess_eq_half {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (g : Graph n → Bool) :
    uprob (fun z : Bool × Equiv.Perm (Fin n) => g (permGraph (cond z.1 G₁ G₀) z.2) = z.1) = 1 / 2 := by
  rw [uprob_bool_prod]
  simp only [cond_false, cond_true]
  rw [uprob_permGraph_eq_of_isomorphic' hσ (fun K => g K = true)]
  have h : uprob (fun σ : Equiv.Perm (Fin n) => g (permGraph G₀ σ) = false) =
      uprob (fun σ : Equiv.Perm (Fin n) => ¬ g (permGraph G₀ σ) = true) :=
    OneWay.uprob_congr fun σ => by simp
  rw [h, uprob_not]
  ring

/-- Shadow of `uprob_gi_cheat_le_half` (Lem-120.c): against non-isomorphic graphs a prover
answers both challenges correctly for no coin string, so it is accepted with probability at
most `1/2`. -/
theorem uprob_gi_cheat_le_half {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : ρ → Graph n) (γ : Bool → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : Bool × ρ => permGraph (cond z.1 G₁ G₀) (γ z.1 z.2) = H z.2) ≤ 1 / 2 := by
  rw [uprob_bool_prod]
  have hsub : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) ≤
      uprob (fun r : ρ => ¬ permGraph (cond true G₁ G₀) (γ true r) = H r) := by
    refine uprob_mono fun r h0 h1 => ?_
    exact not_isomorphic_both h ⟨⟨γ false r, h0⟩, ⟨γ true r, h1⟩⟩
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    have h1 : uprob (fun r : ρ => permGraph (cond true G₁ G₀) (γ true r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0, h1]
    norm_num
  · rw [uprob_not] at hsub
    linarith

end TCSlib.Cryptography.GI


/- ===== gate 07 statement sweep: seal-candidate collector (appended to the statement-only copy) =====
Walks every constant declared in this file (the current module of the statement-only copy, in which
every theorem/lemma/example value is `sorry`): the TYPE of every constant (theorems, definitions,
instances, structures and their fields/constructors/recursors, auxiliaries), and the VALUE of every
definition/instance/abbreviation/opaque (theorem values are `sorry`, so proofs contribute nothing).
Every TCSlib constant declared in another module that occurs there is classified:
* `def` (a plain, non-instance, non-reducible, non-projection, non-auxiliary, non-private
  definition): a seal candidate. Its value and its type are walked further (`deep` tier).
* instance / `@[reducible]` (incl. `abbrev`) / private / auxiliary (matcher, `_unary`, …):
  transparent or unnameable, so not sealed; recorded, and their values and types are walked.
* any other constant (theorem, structure, inductive, constructor, projection, axiom, …): its TYPE is
  walked (using a constant can make the elaborator reduce its type), it is not sealed.
`direct` = occurs in this file's types/values; `deep` = reached only through a foreign constant.
Output: SWEEP_OUT.cands.tsv, SWEEP_OUT.uses.tsv, SWEEP_OUT.transparent.tsv -/
namespace SweepCollect
open Lean
def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit
def isAuxComp (s : String) : Bool :=
  s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
    s == "eq_def" || s == "eq_unfold"
def isAuxName : Name → Bool
  | .str p s => isAuxComp s || isAuxName p
  | .num _ _ => true
  | .anonymous => false
end SweepCollect

open Lean Meta in
run_cmd do
  let env ← getEnv
  let outBase : String := "/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/e1/final6/proofseal/work/TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_Proofs.coll"
  let modNames := env.header.moduleNames
  let isTCS (j : ModuleIdx) : Bool := (modNames[j.toNat]!).getRoot == `TCSlib
  let kindOf (n : Name) : String :=
    match env.find? n with
    | some (.defnInfo _) =>
      if isPrivateName n then "private"
      else if SweepCollect.isAuxName n || isMatcherCore env n || isAuxRecursor env n || isNoConfusion env n then "aux"
      else if env.isProjectionFn n then "proj"
      else if isInstanceCore env n then "instance"
      else if getReducibilityStatusCore env n == .reducible then "reducible"
      else if getReducibilityStatusCore env n == .irreducible then "irreducible"
      else "def"
    | some (.thmInfo _) => "thm"
    | some (.axiomInfo _) => "axiom"
    | some (.opaqueInfo _) => "opaque"
    | some (.inductInfo _) => "inductive"
    | some (.ctorInfo _) => "ctor"
    | some (.recInfo _) => "rec"
    | some (.quotInfo _) => "quot"
    | none => "none"
  -- local constants of this file
  let locals := env.constants.map₂.toList.filter fun (n, _) => !(n.components.contains `SweepCollect)
  -- candidate ↦ (tier, via set, owners)
  let mut cands : Std.HashMap Name (String × NameSet × NameSet) := {}
  let mut transp : Std.HashMap Name (String × NameSet) := {}
  let mut uses : Array String := #[]
  for (ln, ci) in locals do
    -- owner: strip auxiliary components / private prefix
    let owner := (privateToUserName? ln).getD ln
    let roots : Array (Name × String) :=
      (ci.type.getUsedConstantsAsSet.toArray.map (·, "T")) ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray.map (·, "V")
       | _ => #[])
    -- worklist: (constant, region T/V, via (anonymous = direct))
    let mut work : Array (Name × String × Name) := roots.map fun (n, r) => (n, r, Name.anonymous)
    let mut seen : Std.HashSet (Name × String) := {}
    let mut found : Array String := #[]
    while !work.isEmpty do
      let (u, r, via) := work.back!
      work := work.pop
      if seen.contains (u, r) then continue
      seen := seen.insert (u, r)
      let some j := env.getModuleIdxFor? u | continue   -- local or unknown: locals are walked as roots
      unless isTCS j do continue
      let some cu := env.find? u | continue
      let k := kindOf u
      let via' := if via.isAnonymous then u else via
      if k == "def" then
        let tier := if via.isAnonymous then "direct" else "deep"
        let (t0, vs, os) := cands.getD u (tier, {}, {})
        let t1 := if t0 == "direct" || tier == "direct" then "direct" else "deep"
        cands := cands.insert u (t1, if via.isAnonymous then vs else vs.insert via, os.insert owner)
        if via.isAnonymous then found := found.push s!"{u}@{r}"
      else if k == "instance" || k == "reducible" || k == "private" || k == "aux" || k == "proj" then
        let (m0, os) := transp.getD u (k, {})
        transp := transp.insert u (m0, os.insert owner)
      -- walk further: the type always; the value of definitions (sealed or transparent)
      for v in cu.type.getUsedConstantsAsSet.toArray do
        unless seen.contains (v, r) do work := work.push (v, r, via')
      if let .defnInfo dv := cu then
        for v in dv.value.getUsedConstantsAsSet.toArray do
          unless seen.contains (v, r) do work := work.push (v, r, via')
    if !found.isEmpty then
      uses := uses.push s!"{owner}\t{ln}\t{" ".intercalate found.toList}"
  let mut cl : Array String := #[]
  for (n, (t, vs, os)) in cands.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    let vsT := ", ".intercalate ((vs.toArray.qsort Name.lt).toList.take 3 |>.map toString)
    cl := cl.push s!"{n}\t{modNames[j.toNat]!}\t{t}\t{vsT}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".cands.tsv") ("\n".intercalate cl.toList ++ "\n")
  IO.FS.writeFile (outBase ++ ".uses.tsv") ("\n".intercalate uses.toList ++ "\n")
  let mut tl : Array String := #[]
  for (n, (k, os)) in transp.toArray.qsort (fun a b => Name.lt a.1 b.1) do
    let some j := env.getModuleIdxFor? n | continue
    tl := tl.push s!"{n}\t{k}\t{modNames[j.toNat]!}\t{os.size}"
  IO.FS.writeFile (outBase ++ ".transparent.tsv") ("\n".intercalate tl.toList ++ "\n")
  -- own-file dependency graph (for the minimiser's cascade/masking rule): for every local constant,
  -- its declaration line and the declaration lines of the local constants its type/value mentions
  let lineOf (n : Name) : Lean.Elab.Command.CommandElabM Int := do
    let mut cur := n
    for _ in [0:8] do
      if let some r ← Lean.findDeclarationRanges? cur then return (r.range.pos.line : Int)
      if let some u := privateToUserName? cur then
        if let some r ← Lean.findDeclarationRanges? u then return (r.range.pos.line : Int)
      match cur with
      | .str p _ => cur := p
      | .num p _ => cur := p
      | .anonymous => return -1
    return -1
  let localSet : NameSet := locals.foldl (fun s (n, _) => s.insert n) {}
  let mut dl : Array String := #[]
  for (ln, ci) in locals do
    -- theorem values included: top-level theorem values are `sorry` here, but the auxiliary
    -- theorems `D.proof_N` abstracted from a definition's body carry that body's proofs
    let refs := ci.type.getUsedConstantsAsSet.toArray ++
      (match ci with
       | .defnInfo dv => dv.value.getUsedConstantsAsSet.toArray
       | .opaqueInfo ov => ov.value.getUsedConstantsAsSet.toArray
       | .thmInfo tv => tv.value.getUsedConstantsAsSet.toArray
       | _ => #[])
    let mut ls : Array Int := #[]
    for v in refs do
      if localSet.contains v && v != ln then
        let l ← lineOf v
        unless ls.contains l do ls := ls.push l
    let l0 ← lineOf ln
    dl := dl.push s!"{l0}\t{ln}\t{" ".intercalate (ls.toList.map toString)}"
  IO.FS.writeFile (outBase ++ ".deps.tsv") ("\n".intercalate dl.toList ++ "\n")
