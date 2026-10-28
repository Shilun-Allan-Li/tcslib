/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph non-isomorphism and graph isomorphism protocols

The two graph protocols of [PS10, §4.5]: the interactive proof for graph non-isomorphism
[PS10, Protocol 118.3, Proposition 118.4] (unbounded prover, verifier first) and the
interactive proof with efficient prover for graph isomorphism [PS10, Protocol 120.6,
Proposition 120.7] (prover first). Graphs are the Boolean adjacency relations `Graph n` of
`Encoding.lean`, isomorphism is `Isomorphic G₀ G₁ := ∃ σ, σ(G₀) = G₁` (Def-117.e), the string
languages `Liso`, `Lniso` and the witness relation `Riso` are stated on the encoded instance
`⟨encGraph G₀, encGraph G₁⟩` (Def-118.a). Every protocol is given once for a single iteration
and once repeated `|x|` times (the text's "repeat `|G₁|` times"); the concrete probability
lemmas (Lem-119.a–d, Lem-120.a–d) are stated over typed coins with ideal uniform
permutations, and the string-level propositions carry the statistical term of the
rejection-sampled permutations (D10).

**Deviation (D10, Inf-4.2):** the honest parties sample `σ, π ← S_n` by `samplePerm`
(`permFromCoins` at the campaign parameters of `Asymptotic/Permutations.lean`:
`permBits n = Nat.size n` bits per trial and `permTrials n = 2n²` trials per position,
identity on failure), which fails with probability at most `permFailBound n = n · 2^{-n}`;
the single-iteration graph non-isomorphism proof has soundness error `1/2 + permFailBound n`
and the repeated protocols' soundness errors carry the same term. The frozen scratch's
`permFromCoins n n n` (`n` bits per trial) accepts a trial with probability `(n - i) / 2^n`
and would make the prover's permutation the identity almost surely — under which
Theorem 122.3 fails (the third message would reveal `σ⁻¹`).

**Repair (run-3 audit P2-1):** `samplePerm`, `permCoinLen` and `permFailBound` are stated in
terms of the shared `permBits`/`permTrials`, `permFailBound n = n · 2^{-n}` is the closed
form `uprob_permFromCoins_none_le_two_pow`, `statClose_samplePerm` and
`negligible_mul_permFailBound` are proved from the shared lemmas, and the run-2
`permFailBound_le_exp` (bound `n e^{-n/2}` for the local parameters) was removed.
(Run-3 audit P10-3, which reported the private `polyTimeComputable_encSamplePerm` as a
diverged copy of the shared sampler lemma with `n²` trials, is resolved by the same repair:
the string form of the sampler is `GI.sampleStr_poly` of `GraphIsomorphism/Efficiency.lean`,
a derivation of `polyTimeComputable_encPermFromCoins` at the one set of parameters
`permBits`/`permTrials`, and DESIGN.md §2.15 records them.)

**Proof layout (run 4).** This file is at the file-size limit, so the proofs of its theorems
live in the sibling files `GraphIsomorphism/Proofs.lean` (verbatim shadow copies of the
definitions below in the inner namespace `GI`, definitionally equal to them, with the generic
infrastructure), `GraphIsomorphism/Efficiency.lean` (the machines of the honest parties and the
decider of `Riso`) and `GraphIsomorphism/Soundness.lean` (completeness and soundness); each
target below is closed by `exact GI.…`, which type-checks by `rfl`.

**Repair (run-3 audit P10-1, P10-2):** the exact-probability lemmas `uprob_adaptive_guess`
(Lem-119.c) and `uprob_gni_rep_cheat` (Lem-119.b) assume the auxiliary coin type nonempty
(`[Nonempty W]`, `[Nonempty ρ]`): `uprob` on an empty type is `0`, so the run-2 statements
read `0 = 1` at `m = 0` over `Empty`. Every consumer instantiates the coin type with a tape
`Fin k → Bool` (nonempty), so no downstream statement changes; `uprob_gi_rep_cheat_le`
(an inequality, true for empty coins) is reproved by a case split on `ρ`. Both corrected
lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the change of
variables `gniShear`), which certifies the repaired statements.

**Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).

**Deviation (well-formedness):** the verifiers reject common inputs that are not the
encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
malformed `x ∉ L` could decode to a pair of isomorphic graphs and soundness would fail.

## Contents

* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs` — shadow copies of the
  definitions of this file (namespace `GI`) and the generic proof infrastructure.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency` — the machines of the honest
  parties of the single iterations and the decider of `Riso`.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep` — the loop infrastructure
  of the `|x|`-fold parties and the machine of the `|x|`-fold graph non-isomorphism verifier.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI` — the machines of the
  parties of the `|x|`-fold graph isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness` — completeness and soundness of
  the single iterations.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete` — shadow copies of the concrete
  repetition lemmas (Lem-119.b, Lem-119.c, Lem-120.d) for the sibling proofs.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep` — completeness and soundness
  of the `|x|`-fold graph non-isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI` — completeness and
  soundness of the `|x|`-fold graph isomorphism protocol.

## Main definitions

* `TCSlib.Cryptography.Isomorphic` — `∃ σ, σ(G₀) = G₁` [PS10, §4.5] (Def-117.e).
* `TCSlib.Cryptography.Liso`, `TCSlib.Cryptography.Lniso`, `TCSlib.Cryptography.Riso` —
  the languages of isomorphic / non-isomorphic encoded pairs and the witness relation
  (Def-118.a); `encInstance`, `wellFormedInstance`, `instanceVertices`.
* `TCSlib.Cryptography.samplePerm`, `TCSlib.Cryptography.permFailBound` — the honest parties'
  permutation sampler and its failure bound (D10).
* `TCSlib.Cryptography.gniProtocol`, `TCSlib.Cryptography.gniProtocolRep` — the graph
  non-isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 118.3]
  (Prot-118.3).
* `TCSlib.Cryptography.giProtocol`, `TCSlib.Cryptography.giProtocolRep` — the graph
  isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 120.6]
  (Prot-120.6).

## Main results

* `TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic` — uniformly permuted isomorphic
  graphs are identically distributed (Lem-119.a, proved).
* `TCSlib.Cryptography.uprob_adaptive_guess` — the adaptive guessing lemma `2^{-m}`
  (Lem-119.c, proved); `TCSlib.Cryptography.uprob_gni_rep_cheat` — `n`-fold GNI soundness
  (Lem-119.b, proved); `TCSlib.Cryptography.gni_honest_reply` — GNI completeness (Lem-119.d,
  proved).
* `TCSlib.Cryptography.gi_honest_reply_eq` (Lem-120.a, proved),
  `TCSlib.Cryptography.not_isomorphic_both` (Lem-120.b, proved),
  `TCSlib.Cryptography.uprob_gi_cheat_le_half` (Lem-120.c, proved),
  `TCSlib.Cryptography.uprob_gi_rep_cheat_le` (Lem-120.d, proved from Lem-119.c).
* `TCSlib.Cryptography.gni_interactiveProofErr`, `TCSlib.Cryptography.gni_interactiveProof`
  — [PS10, Proposition 118.4]; `TCSlib.Cryptography.gi_efficientProverProofErr`,
  `TCSlib.Cryptography.gi_rep_efficientProverProof` — [PS10, Proposition 120.7].
* `TCSlib.Cryptography.Riso_witnessRelation` — `Riso` is a witness relation for `Liso`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, the graph non-isomorphism protocol.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Isomorphism of graphs (Def-117.e) -/

/-- Two graphs on `Fin n` are isomorphic when some relabelling `σ` maps the first onto the
second, `σ(G₀) = G₁` [PS10, §4.5] (Def-117.e). The "same number of vertices" condition of
the text is the common type `Graph n`. -/
def Isomorphic {n : ℕ} (G₀ G₁ : Graph n) : Prop := ∃ σ : Equiv.Perm (Fin n), permGraph G₀ σ = G₁

/-- Isomorphism is decidable (finitely many permutations). -/
instance {n : ℕ} (G₀ G₁ : Graph n) : Decidable (Isomorphic G₀ G₁) := by
  unfold Isomorphic
  infer_instance

/-- Every graph is isomorphic to itself (via the identity). -/
theorem Isomorphic.refl {n : ℕ} (G : Graph n) : Isomorphic G G := ⟨1, permGraph_one G⟩

/-- Isomorphism is symmetric (via the inverse permutation). -/
theorem Isomorphic.symm {n : ℕ} {G₀ G₁ : Graph n} (h : Isomorphic G₀ G₁) : Isomorphic G₁ G₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, permGraph_permGraph_inv]⟩

/-- Isomorphism is transitive (via the product of the permutations). -/
theorem Isomorphic.trans {n : ℕ} {G₀ G₁ G₂ : Graph n} (h₁ : Isomorphic G₀ G₁)
    (h₂ : Isomorphic G₁ G₂) : Isomorphic G₀ G₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [← permGraph_mul, hσ, hτ]⟩

/-- A graph is isomorphic to each of its relabellings. -/
theorem isomorphic_permGraph {n : ℕ} (G : Graph n) (σ : Equiv.Perm (Fin n)) :
    Isomorphic G (permGraph G σ) := ⟨σ, rfl⟩

/-- Relabelling by a fixed permutation is injective on graphs. -/
theorem permGraph_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective fun G : Graph n => permGraph G σ := by
  intro G G' h
  have := congrArg (fun K => permGraph K σ⁻¹) h
  simpa only [permGraph_permGraph_inv] using this

/-- A graph is isomorphic to at most one of two non-isomorphic graphs [PS10, proof of
Proposition 120.7, "`H` can be isomorphic to at most one of them"] (Lem-120.b): by symmetry
and transitivity of `Isomorphic`. -/
theorem not_isomorphic_both {n : ℕ} {G₀ G₁ H : Graph n} (h : ¬ Isomorphic G₀ G₁) :
    ¬ (Isomorphic G₀ H ∧ Isomorphic G₁ H) := fun ⟨h₀, h₁⟩ => h (h₀.trans h₁.symm)

/-- The honest prover's third message is accepted whatever the challenge [PS10, proof of
Proposition 120.7, corrected: `π(G₀) = H` and `(π σ⁻¹)(G₁) = H`] (Lem-120.a): if
`σ(G₀) = G₁` then `γ(G_b) = π(G₀)` for `γ = if b then π σ⁻¹ else π`. -/
theorem gi_honest_reply_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) (b : Bool) :
    permGraph (cond b G₁ G₀) (if b then π * σ⁻¹ else π) = permGraph G₀ π := by
  cases b
  · rfl
  · exact permGraph_mul_inv_of_eq hσ π

/-! ### Encoded instances and the languages (Def-118.a) -/

/-- The total decoding of a graph on a *given* vertex count `n` (entries read with default
`false`): the second component of `decGraph` at `n`, used to read the other party's graph
message on the vertex set of the common input. -/
def decGraphAt (n : ℕ) (w : List Bool) : Graph n := fun u v => w.getD (finProdFinEquiv (u, v)) false

/-- Decoding an encoded graph on its own vertex count gives the graph back. -/
@[simp] theorem decGraphAt_encGraph {n : ℕ} (G : Graph n) : decGraphAt n (encGraph G) = G :=
  funext fun u => funext fun v => encGraph_getD G u v

/-- The second component of `decGraph` is `decGraphAt` at the decoded vertex count. -/
theorem decGraph_snd (w : List Bool) : (decGraph w).2 = decGraphAt (decGraph w).1 w := rfl

/-- The encoded instance `x = ⟨encGraph G₀, encGraph G₁⟩` of the graph protocols
[PS10, Protocols 118.3 and 120.6, "`x = (G₀, G₁)`"]. -/
def encInstance {n : ℕ} (G₀ G₁ : Graph n) : List Bool := pairEncode (encGraph G₀) (encGraph G₁)

/-- An encoded instance on `n` vertices has `3n² + 2` bits. -/
theorem length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : (encInstance G₀ G₁).length = 3 * (n * n) + 2 := by
  simp only [encInstance, length_pairEncode, length_encGraph]
  ring

/-- The vertex count read from a common input: `Nat.sqrt` of the length of the first
component (the `n` of `decGraph`). -/
def instanceVertexCount (x : List Bool) : ℕ := Nat.sqrt (pairFstD x).length

/-- The first graph of a common input, on the decoded vertex set. -/
def instanceG₀ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairFstD x)

/-- The second graph of a common input, on the vertex set of the first. -/
def instanceG₁ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairSndD x)

/-- A common input is well formed when it is a pair whose two components are adjacency
matrices of the same size `n²` (the "same number of vertices" of [PS10, §4.5]). -/
def wellFormedInstance (x : List Bool) : Bool :=
  decide ((pairDecode x).isSome ∧ (pairFstD x).length = instanceVertexCount x * instanceVertexCount x ∧
    (pairSndD x).length = instanceVertexCount x * instanceVertexCount x)

/-- The vertex count of an encoded instance from its length: `n = √((|x| - 2) / 3)`. -/
def instanceVertices (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 3)

/-- `instanceVertices` recovers `n` from the length of an encoded instance on `n` vertices. -/
theorem instanceVertices_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertices (encInstance G₀ G₁).length = n := by
  rw [instanceVertices, length_encInstance, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.sqrt_eq]

/-- The vertex count decoded from an encoded instance is `n`. -/
theorem instanceVertexCount_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertexCount (encInstance G₀ G₁) = n := by
  simp [instanceVertexCount, encInstance, Nat.sqrt_eq]

/-- The language of pairs of isomorphic graphs, `L_iso` [PS10, §4.5] (Def-118.a): the encoded
instances `⟨encGraph G₀, encGraph G₁⟩` with `σ(G₀) = G₁` for some `σ`. -/
def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

/-- The language of pairs of non-isomorphic graphs with the same number of vertices,
`L_niso` [PS10, §4.5] (Def-118.a); malformed strings are not in `L_niso`. -/
def Lniso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n), x = pairEncode (encGraph G₀) (encGraph G₁) ∧ ¬ Isomorphic G₀ G₁}

/-- The witness relation of `L_iso` [PS10, Theorem 122.3, "some canonical witness relation"]
(Def-118.a): the witness of `⟨encGraph G₀, encGraph G₁⟩` is the encoding of a permutation `σ`
with `σ(G₀) = G₁`. -/
def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

/-- Equal encodings come from the same vertex count and the same graph (as a `Sigma`). -/
private theorem sigma_eq_of_encGraph_eq {n n' : ℕ} {G : Graph n} {G' : Graph n'}
    (h : encGraph G = encGraph G') : (⟨n, G⟩ : Σ m, Graph m) = ⟨n', G'⟩ := by
  rw [← decGraph_encGraph G, ← decGraph_encGraph G', h]

/-- An encoded instance is in `L_iso` exactly when its graphs are isomorphic. -/
theorem encInstance_mem_Liso_iff {n : ℕ} (G₀ G₁ : Graph n) : encInstance G₀ G₁ ∈ Liso ↔ Isomorphic G₀ G₁ := by
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

/-- The languages `L_iso` and `L_niso` are disjoint. -/
theorem not_mem_Lniso_of_mem_Liso {x : List Bool} (h : x ∈ Liso) : x ∉ Lniso := by
  obtain ⟨n, G₀, G₁, σ, rfl, hσ⟩ := h
  rw [show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
    encInstance_mem_Lniso_iff]
  exact fun hni => hni ⟨σ, hσ⟩

/-- `Riso` is a witness relation for `L_iso` [PS10, Definition 191.11 for Theorem 122.3]
(Def-118.a).

**Proof sketch.** `mem_iff`: both sides unfold to the same existential (the witness of
`⟨encGraph G₀, encGraph G₁⟩` is `encPerm σ`). `bounded` with `p := var`: `|encPerm σ| = n² ≤
3n² + 2 = |x|` (`length_encPerm`, `length_encInstance`). `decidable`: the predicate
`T z := wellFormedInstance x && decide (encPerm (decPerm n y) = y) &&
decide (encGraph (permGraph G₀ (decPerm n y)) = pairSndD x)` with `x := pairFstD z`,
`y := pairSndD z`, `n := instanceVertexCount x`; it is polynomial-time by
`Complexity.polyTimeComputable_and`, `polyTimeComputable_pairEq`, `polyTimeComputable_lenEq`
and `polyTimeComputable_encPermGraph` composed with the pairing projections (the identity
`encPerm ∘ decPerm` test is a scan of the `n²` bits with the row/column uniqueness check of
`decPerm`'s sketch); on well-formed inputs `T ⟨x, y⟩ = true ↔ Riso x y` by
`decGraph_encGraph`, `decPerm_encPerm`, `encGraph_injective`, `encPerm_injective` and the
well-formedness characterization of `wellFormedInstance`. -/
theorem Riso_witnessRelation : WitnessRelation Liso Riso := by
  refine ⟨fun x => ?_, ⟨.var, ?_⟩, ?_⟩
  · constructor
    · rintro ⟨n, G₀, G₁, σ, hx, hσ⟩
      exact ⟨encPerm σ, n, G₀, G₁, σ, hx, rfl, hσ⟩
    · rintro ⟨y, n, G₀, G₁, σ, hx, -, hσ⟩
      exact ⟨n, G₀, G₁, σ, hx, hσ⟩
  · rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, -⟩
    rw [PolyExpr.eval_var, length_encPerm, show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
      length_encInstance]
    omega
  · exact GI.Riso_decidable

/-! ### The permutation sampler of the honest parties (D10) -/

/-- The honest parties' permutation sampler: `permFromCoins` at the campaign parameters
(`permBits n = Nat.size n` bits per trial, so that `n ≤ 2^k ≤ 2n`, and `permTrials n = 2n²`
trials per position), read from the tape by `coinTable`; the identity on failure
[PS10, Protocols 118.3 and 120.6, "`σ ← S_n`", "`π ← S_n`"] (D10).

**Repair (run-3 audit P2-1):** parameters taken from `Asymptotic/Permutations.lean`
(the run-2 file used `Nat.size n` bits and `n²` trials locally). -/
noncomputable def samplePerm (n : ℕ) (r : List Bool) : Equiv.Perm (Fin n) :=
  (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1

/-- The number of tape bits consumed by `samplePerm n`: `n · permTrials n · permBits n`
(`= 2n³ · Nat.size n`).

**Repair (run-3 audit P2-1):** stated in terms of `permTrials`/`permBits`. -/
def permCoinLen (n : ℕ) : ℕ := n * permTrials n * permBits n

/-- The failure bound of the permutation sampler at the campaign parameters, `n · 2^{-n}`
(`uprob_permFromCoins_none_le_two_pow`).

**Repair (run-3 audit P2-1):** the run-2 bound `n (1 - 2^{-size n})^{n²}` had no closed form;
the closed form `n · 2^{-n}` is owned by `Asymptotic/Permutations.lean`. -/
noncomputable def permFailBound (n : ℕ) : ℝ := n * (2 : ℝ)⁻¹ ^ n

/-- The sampler consumes at most `(N + 1)²` tape bits whenever `2n² ≤ N` (every encoded
instance on `n` vertices has length `3n² + 2`, `length_encInstance`), so the coin polynomial
`normal 1 2` of the parties suffices: `n · 2n² · permBits n ≤ 2n⁴ ≤ N² ≤ (N + 1)²`.

**Repair (run-3 audit P2-1):** hypothesis strengthened from `n² ≤ N` to `2n² ≤ N` to absorb
the factor `2` of `permTrials` (satisfied by every encoded instance). -/
theorem permCoinLen_le {n N : ℕ} (h : 2 * (n * n) ≤ N) : permCoinLen n ≤ (N + 1) ^ 2 := by
  have hnn : n * n ≤ N := le_trans (Nat.le_mul_of_pos_left (n * n) two_pos) h
  calc permCoinLen n = n * (2 * n * n) * permBits n := rfl
    _ ≤ n * (2 * n * n) * n := Nat.mul_le_mul_left _ (permBits_le n)
    _ = (2 * (n * n)) * (n * n) := by ring
    _ ≤ N * N := Nat.mul_le_mul h hnn
    _ ≤ (N + 1) ^ 2 := by nlinarith

/-- The permutation sampler is within `permFailBound n = n · 2^{-n}` of a uniform permutation
(D10): `pushesUniform_coinTable` identifies the tape with a uniform coin table
(`StatClose.comp_pushesUniform`) and `statClose_permFromCoins_two_pow` is the closeness of
`permFromCoins` at the campaign parameters.

**Repair (run-3 audit P2-1):** proved from the shared lemmas of
`Asymptotic/Permutations.lean` (previously sorried with the argument restated). -/
theorem statClose_samplePerm (n : ℕ) :
    StatClose (fun r : Fin (permCoinLen n) → Bool => samplePerm n (List.ofFn r))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) :=
  (statClose_permFromCoins_two_pow n 1).comp_pushesUniform
    (pushesUniform_coinTable n (permTrials n) (permBits n))

/-- The sampling error of the repeated protocols, `|x| · permFailBound n` with
`n = instanceVertices |x|`, is negligible in `|x|` (Inf-4.4): for `N ≥ 8`,
`√(N/4) ≤ instanceVertices N ≤ N`, so the term is at most `N² · 2^{-√(N/4)}`
(`negligible_two_pow_neg_sqrt_div`, `Negligible.mul_pow`, `Negligible.mono`).

**Repair (run-3 audit P2-1):** proved (the run-2 sketch went through `permFailBound_le_exp`,
removed). -/
theorem negligible_mul_permFailBound :
    Negligible fun N : ℕ => (N : ℝ) * permFailBound (instanceVertices N) := by
  refine ((negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mul_pow 2).mono
    ⟨8, fun N hN => ?_⟩
  have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
  have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
  have hpow : (2 : ℝ)⁻¹ ^ instanceVertices N ≤ (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have hv' : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
  unfold permFailBound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (N : ℝ) * (instanceVertices N * (2 : ℝ)⁻¹ ^ instanceVertices N)
      ≤ N * (N * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4)) := by gcongr
    _ = (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) := by ring

/-- The `i`-th block of `c` bits of a tape (the coins of iteration `i` of a repeated
protocol). -/
def coinSlice (c i : ℕ) (r : List Bool) : List Bool := (r.drop (i * c)).take c

/-! ### The graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3) -/

/-- The honest (unbounded) prover of the graph non-isomorphism protocol [PS10, Protocol
118.3]: on the latest received graph `H` it answers `b' = 0` if `H ≅ G₀` and `b' = 1`
otherwise (so `b' = b` whenever `G₀ ≇ G₁`); no coins, no auxiliary input. The text's
"exponential time" is the search over all permutations in the `Decidable` instance. -/
def gniProver : Strategy where
  coins := .const 0
  next x _ _ hist :=
    [decide (¬ Isomorphic (instanceG₀ x) (decGraphAt (instanceVertexCount x) (hist.getLastD [])))]

/-- The verifier of one iteration of the graph non-isomorphism protocol [PS10, Protocol
118.3]: with random tape `b :: r`, it first sends `H = σ(G_b)` for `σ := samplePerm n r`, and
on the reply `b'` outputs `[decide (x well formed ∧ b' = b)]`.

**Deviation:** `σ` by rejection sampling (D10); well-formedness check on `x`. -/
noncomputable def gniVerifier : Strategy where
  coins := .add (.const 1) (.normal 1 2)
  next x _ r hist :=
    let b := r.headD false
    match hist with
    | [] => encGraph (permGraph (if b then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (r.drop 1)))
    | [b'] => [decide (wellFormedInstance x = true ∧ b'.headD false = b)]
    | _ => [false]

/-- One iteration of the graph non-isomorphism protocol [PS10, Protocol 118.3]
(Prot-118.3): verifier first, two messages (`H`, then `b'`); the verdict is the verifier's
third activation. -/
noncomputable def gniProtocol : Protocol where
  P := gniProver
  V := gniVerifier
  rounds := .const 2
  verifierFirst := true

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3,
"repeat the procedure `|G₁|` times"]: iteration `i` uses the coin block
`coinSlice (1 + (|x|+1)²) i r` (bit `b_i`, then the permutation coins); after `i < |x|`
replies it sends `H_i`, and on the complete history of `|x|` replies it accepts iff `x` is
well formed and every reply `b'_i` equals `b_i`.

**Deviation:** `|x|` iterations instead of `n`; rejection-sampled `σ_i` (D10). -/
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

/-- The `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3):
verifier first, `2|x|` messages; the honest prover answers each `H_i` as in one iteration. -/
noncomputable def gniProtocolRep : Protocol where
  P := gniProver
  V := gniVerifierRep
  rounds := .mul (.const 2) .var
  verifierFirst := true

/-! ### The graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6) -/

/-- The prover of the graph isomorphism protocol [PS10, Protocol 120.6]: with witness
`y = encPerm σ` it samples `π ← S_n` from its tape, sends `H = π(G₀)`, and on the challenge
`b` sends `γ = if b then π σ⁻¹ else π` (so that `γ(G_b) = H`, `gi_honest_reply_eq`).

**Deviation (D10):** `π` by `samplePerm` (rejection sampling, identity on failure). -/
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

/-- The verifier of the graph isomorphism protocol [PS10, Protocol 120.6]: with the single
coin `b` it answers the first message `H` with `[b]`, and on `[H, γ]` outputs
`[decide (x well formed ∧ γ(G_b) = H)]`.

**Deviation:** well-formedness check on `x` (needed for soundness on malformed inputs). -/
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

/-- One iteration of the graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6):
three messages (`H`, `b`, `γ`), prover first; the verdict is the verifier's activation on
the complete history `[H, γ]`. -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

/-- The prover of the `|x|`-fold graph isomorphism protocol: iteration `i` (the prover has
received `2i` or `2i + 1` messages: the challenges and the verifier's empty fourth messages)
uses `π_i := samplePerm n (coinSlice (|x|+1)² i r)`; on an even history it sends `H_i`, on an
odd one `γ_i` for the latest challenge. -/
noncomputable def giProverRep : Strategy where
  coins := .mul .var (.normal 1 2)
  next x y r hist :=
    let n := instanceVertexCount x
    let σ := decPerm n y
    let π := samplePerm n (coinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)
    if hist.length % 2 = 0 then encGraph (permGraph (instanceG₀ x) π)
    else encPerm (if (hist.getLastD []).headD false then π * σ⁻¹ else π)

/-- The verifier of the `|x|`-fold graph isomorphism protocol: it has received
`[H_0, γ_0, H_1, γ_1, …]`; on an odd history it sends the challenge `b_i = r_i`, on an even
incomplete history the empty message, and on the complete history it accepts iff `x` is
well formed and `γ_j(G_{b_j}) = H_j` for every `j < |x|`. -/
noncomputable def giVerifierRep : Strategy where
  coins := .var
  next x _ r hist :=
    let n := instanceVertexCount x
    if hist.length % 2 = 1 then [r.getD (hist.length / 2) false]
    else if hist.length < 2 * x.length then []
    else [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
      encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm n (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])]

/-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
`|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
noncomputable def giProtocolRep : Protocol where
  P := giProverRep
  V := giVerifierRep
  rounds := .mul (.const 4) .var
  verifierFirst := false

/-! ### Concrete probability lemmas (ideal uniform permutations) -/

/-- Uniformly permuted isomorphic graphs are identically distributed, jointly with
independent auxiliary coins [PS10, proof of Lemma 123.5 and of Proposition 118.4,
"`H` is independent of the bit `b`"] (Lem-119.a): if `σ₀(G₀) = G₁` then
`σ(G₁) = (σ σ₀)(G₀)` and `σ ↦ σ σ₀` is a bijection of `S_n` (`Equiv.mulRight`). -/
theorem uprob_permGraph_eq_of_isomorphic {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → ρ → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₁ z.1) z.2) =
      uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2) := by
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.mulRight σ₀) (Equiv.refl ρ))
    (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2)]
  congr 1
  funext z
  simp [← hσ, permGraph_mul]

/-- The one-coordinate form of Lem-119.a: `σ(G₁)` and `σ(G₀)` have the same law. -/
theorem uprob_permGraph_eq_of_isomorphic' {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → Prop) :
    uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₁ σ)) =
      uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ)) := by
  rw [← uprob_comp_equiv (Equiv.mulRight σ₀) (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ))]
  congr 1
  funext σ
  simp [← hσ, permGraph_mul]

/-- The strict prefix `b_0, …, b_{i-1}` of a bit tuple (the history an adaptive prover has
seen before challenge `i`). -/
def prefixLT {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin i → α :=
  fun j => b (Fin.castLE i.isLt.le j)

/-- The prefix `b_0, …, b_i` of a tuple (the history including the current challenge). -/
def prefixLE {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin (i + 1) → α :=
  fun j => b (Fin.castLE i.isLt j)

/-- The adaptive guess map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` of Lem-119.c: triangular with
identity diagonal, hence a bijection of `Fin m → Bool` for every `w` (`adaptiveXorEquiv`); it
carries the event "`b_i = g_i(b_{<i}, w)` for every `i`" to "`b = 0`". -/
private def adaptiveXor {m : ℕ} {W : Type*} (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W)
    (b : Fin m → Bool) : Fin m → Bool :=
  fun i => xor (b i) (g i (prefixLT b i) w)

/-- `adaptiveXor g w` is injective.

**Proof sketch.** If the images agree then `b_i = b'_i` for every `i`, by induction on a bound
`k > i`: the prefixes `b_{<i}`, `b'_{<i}` agree by the induction hypothesis, so the guesses
`g_i(b_{<i}, w)`, `g_i(b'_{<i}, w)` agree and `xor` cancels (`Bool.xor_left_inj`). -/
private theorem adaptiveXor_injective {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) :
    Function.Injective (adaptiveXor g w) := by
  intro b b' h
  have key : ∀ k, ∀ i : Fin m, i.val < k → b i = b' i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hpre : prefixLT b i = prefixLT b' i := by
          funext j
          have hj := j.isLt
          exact ih _ (by simp only [Fin.coe_castLE]; omega)
        have hi' := congrFun h i
        simp only [adaptiveXor, hpre] at hi'
        exact Bool.xor_left_inj.mp hi'
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The bijection `adaptiveXor g w` of `Fin m → Bool` (an injection of a finite type into
itself, `Finite.injective_iff_bijective`). -/
private noncomputable def adaptiveXorEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.ofBijective (adaptiveXor g w)
    (Finite.injective_iff_bijective.mp (adaptiveXor_injective g w))

/-- The coin bijection `(b, w) ↦ (adaptiveXor g w b, w)` of `(Fin m → Bool) × W`. -/
private noncomputable def adaptiveEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) : (Fin m → Bool) × W ≃ (Fin m → Bool) × W where
  toFun z := (adaptiveXorEquiv g z.2 z.1, z.2)
  invFun z := ((adaptiveXorEquiv g z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The adaptive guessing lemma [PS10, proof of Proposition 118.4, "each iteration is
independent of all prior iterations"] (Lem-119.c): for every finite nonempty `W` and every
family of guesses `g i` depending on the earlier bits and on `w`, the probability that a
uniform tuple `b` satisfies `b_i = g_i(b_{<i}, w)` for every `i` is exactly `2^{-m}`. The
engine of every `2^{-n}` soundness bound against adaptive provers.

**Deviation:** `W` nonempty (`uprob` on an empty type is `0`, so the equality fails for
`W = Empty`; every consumer uses a tape type `Fin k → Bool`).

**Repair (run-3 audit P10-1):** hypothesis `[Nonempty W]` added (the run-2 statement
specialised to `W := Empty`, `m := 0` reads `0 = 1`).

**Proof sketch.** For each `w` the map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` is a bijection of
`Fin m → Bool` (`adaptiveXorEquiv`: triangular with identity diagonal, injective by strong
induction on `i`, hence bijective on a finite type) carrying the event to `{b = 0}`; so
`uprob_comp_equiv` with the coin bijection `adaptiveEquiv`, `uprob_fst` (here `W ≠ ∅` is
used) and `OneWay.uprob_eq_one_div_card` give `1 / 2^m` (`Fintype.card_fun`). Equivalently,
exactly one `b` per `w` satisfies all the constraints (`|W|` elements out of `2^m |W|`). -/
theorem uprob_adaptive_guess (m : ℕ) {W : Type*} [Fintype W] [Nonempty W]
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) :
    uprob (fun z : (Fin m → Bool) × W => ∀ i, z.1 i = g i (prefixLT z.1 i) z.2) =
      (2 : ℝ)⁻¹ ^ m := by
  have hev : ∀ z : (Fin m → Bool) × W,
      (∀ i, z.1 i = g i (prefixLT z.1 i) z.2) ↔ (adaptiveEquiv g z).1 = fun _ => false := by
    intro z
    simp only [adaptiveEquiv, adaptiveXorEquiv, Equiv.coe_fn_mk, Equiv.ofBijective_apply,
      adaptiveXor, funext_iff]
    exact forall_congr' fun i => by cases z.1 i <;> cases g i (prefixLT z.1 i) z.2 <;> simp
  rw [OneWay.uprob_congr hev,
    uprob_comp_equiv (adaptiveEquiv g) (fun z : (Fin m → Bool) × W => z.1 = fun _ => false),
    uprob_fst (β := W) (fun b : Fin m → Bool => b = fun _ => false),
    OneWay.uprob_eq_one_div_card (fun _ : Fin m => false), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow]

/-- Soundness of one iteration of the graph isomorphism protocol against an arbitrary
prover [PS10, proof of Proposition 120.7] (Lem-120.c): if `G₀ ≇ G₁` then, for a prover
whose first message is `H(r)` and whose reply to the challenge `b` is `γ(b, r)`, the verifier
accepts with probability at most `1/2` over the uniform `b` and the prover's coins `r`.

**Proof sketch.** `uprob_bool_prod`; for each `r` at most one `b` can be accepted
(`not_isomorphic_both`), so the `b = false` event is contained in the complement of the
`b = true` event (`uprob_mono`, `uprob_not`). -/
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

/-- Soundness of the `m`-fold graph isomorphism protocol against adaptive provers
[PS10, Proposition 120.7, "repeated … to drive the error as low as desired"] (Lem-120.d):
if `G₀ ≇ G₁` then for a prover whose `i`-th graph `H_i` depends on the earlier challenges and
its coins and whose `i`-th reply `γ_i` also depends on the current challenge, the verifier
accepts all `m` iterations with probability at most `2^{-m}`.

**Proof sketch.** For empty `ρ` the probability is `0`. Otherwise acceptance in iteration `i` forces
`b_i = g_i(b_{<i}, r)` for the guess `g_i := decide (G₁ ≅ H_i)` (`not_isomorphic_both`), so
`uprob_mono` reduces to `uprob_adaptive_guess`.

**Repair (run-3 audit P10-1):** statement unchanged (an inequality, true for empty coins);
the proof splits on `ρ` empty since `uprob_adaptive_guess` now assumes `Nonempty`. -/
theorem uprob_gi_rep_cheat_le {n m : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : (i : Fin m) → (Fin i → Bool) → ρ → Graph n)
    (γ : (i : Fin m) → (Fin (i + 1) → Bool) → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
      permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) ≤
      (2 : ℝ)⁻¹ ^ m := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
        permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) = 0 := by
      classical
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0]
    positivity
  · rw [← uprob_adaptive_guess m fun i p r => decide (Isomorphic G₁ (H i p r))]
    refine uprob_mono fun z hz i => ?_
    have hi := hz i
    cases hb : z.1 i
    · rw [hb] at hi
      have h0 : Isomorphic G₀ (H i (prefixLT z.1 i) z.2) := ⟨_, hi⟩
      exact (decide_eq_false fun h1 => not_isomorphic_both h ⟨h0, h1⟩).symm
    · rw [hb] at hi
      exact (decide_eq_true ⟨_, hi⟩).symm

/-- The change of variables of Lem-119.b, `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, with the
coins regrouped as `(b, (σ, w))` (inverse: multiply by `σ₀` instead). -/
private def gniShear {n m : ℕ} (ρ : Type*) (σ₀ : Equiv.Perm (Fin n)) :
    (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ) ≃
      ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ where
  toFun z := ((z.1, fun i => if z.1 i then z.2.1 i * σ₀⁻¹ else z.2.1 i), z.2.2)
  invFun z := (z.1.1, (fun i => if z.1.1 i then z.1.2 i * σ₀ else z.1.2 i, z.2))
  left_inv z := by
    rcases z with ⟨b, σ, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp
  right_inv z := by
    rcases z with ⟨⟨b, σ⟩, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp

/-- Under `gniShear` every graph `H_j = σ'_j(G₀)` is independent of `b`
(`permGraph_mul_inv_of_eq`), so the event "every reply equals the verifier's bit" is the
adaptive guessing event of `uprob_adaptive_guess` with guesses ignoring the earlier bits. -/
private theorem gniShear_event_iff {n m : ℕ} {ρ : Type*} {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    ∀ z : (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ),
      (∀ i, g i (prefixLE (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ z).1.1 j) G₁ G₀)
          ((gniShear (m := m) ρ σ₀ z).1.2 j)) i) (gniShear (m := m) ρ σ₀ z).2 =
            (gniShear (m := m) ρ σ₀ z).1.1 i) ↔
      (∀ i, z.1 i = g i (prefixLE (fun j => permGraph G₀ (z.2.1 j)) i) z.2.2) := by
  rintro ⟨b, σ, w⟩
  have hH : (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.1 j) G₁ G₀)
      ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.2 j)) = fun j => permGraph G₀ (σ j) := by
    funext j
    show permGraph (cond (b j) G₁ G₀) (if b j then σ j * σ₀⁻¹ else σ j) = permGraph G₀ (σ j)
    cases b j
    · rfl
    · exact permGraph_mul_inv_of_eq hσ (σ j)
  rw [hH]
  exact forall_congr' fun i => eq_comm

/-- Soundness of the `m`-fold graph non-isomorphism protocol against adaptive provers
[PS10, proof of Proposition 118.4] (Lem-119.b): if `σ₀(G₀) = G₁`, then for every prover
whose `i`-th reply `g_i` depends on the graphs `H_0, …, H_i` received so far and on its
(nonempty type of) coins `w`, the probability (over the verifier's bits `b`, permutations `σ`
and `w`) that every reply equals the verifier's bit is exactly `2^{-m}`.

**Deviation:** `ρ` nonempty (`uprob` on an empty type is `0`; the consumer
`gni_interactiveProof` uses `ρ := P'.Coins |x|`, a tape type).

**Repair (run-3 audit P10-2):** hypothesis `[Nonempty ρ]` added (the run-2 statement
specialised to `ρ := Empty`, `n = m = 0`, `σ₀ = 1` reads `0 = 1`).

**Proof sketch.** Change variables `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, a bijection of the
coins fixing `b` and `w` (`gniShear`, with `uprob_comp_equiv`); then every `H_i = σ'_i(G₀)`
(`permGraph_mul_inv_of_eq`, `hσ`) is a function of `σ'` alone, the event is
`∀ i, b_i = g'_i(b_{<i}, (σ', w))` with `g'_i` ignoring `b_{<i}` (`gniShear_event_iff`), and
`uprob_adaptive_guess` with `W := (Fin m → S_n) × ρ` (nonempty since `ρ` is) gives
`2^{-m}`. -/
theorem uprob_gni_rep_cheat {n m : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    uprob (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i) =
      (2 : ℝ)⁻¹ ^ m := by
  have h1 := uprob_comp_equiv (gniShear (m := m) ρ σ₀)
    (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i)
  have h2 := uprob_adaptive_guess m
    fun i (_ : Fin i → Bool) (w : (Fin m → Equiv.Perm (Fin n)) × ρ) =>
      g i (prefixLE (fun j => permGraph G₀ (w.1 j)) i) w.2
  rw [← h1, ← h2]
  exact OneWay.uprob_congr (gniShear_event_iff hσ g)

/-- Completeness of the graph non-isomorphism protocol [PS10, proof of Proposition 118.4,
"the prover will always succeed in finding `b'` such that `b' = b`"] (Lem-119.d): if
`G₀ ≇ G₁` then for every `b` and `σ` the honest reply `decide (¬ G₀ ≅ σ(G_b))` is `b`. -/
theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (b : Bool)
    (σ : Equiv.Perm (Fin n)) :
    decide (¬ Isomorphic G₀ (permGraph (cond b G₁ G₀) σ)) = b := by
  cases b
  · exact decide_eq_false (not_not.2 (isomorphic_permGraph G₀ σ))
  · exact decide_eq_true fun h' => h (h'.trans (isomorphic_permGraph G₁ σ).symm)

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of the graph isomorphism protocol is a PPT strategy
[PS10, Proposition 120.7, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^n, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`,
`polyTimeComputable_inArg`): `encPerm π` by `polyTimeComputable_encSamplePerm` on
`⟨x, r⟩`; message 1 by `polyTimeComputable_encPermGraph` on `⟨pairFstD x, encPerm π⟩`;
message 3 by `polyTimeComputable_encPermMulInv` on `⟨encPerm π, y⟩` (branch on the challenge
bit `pairFstD msgs` with `polyTimeComputable_ite`; the `γ = π` branch outputs `encPerm π`),
the case split on `msgs = []` by `polyTimeComputable_lenEq`; the equation with `giProver.next`
by `NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`, `decPerm_encPerm`. -/
theorem giProver_efficient : giProver.Efficient := GI.giProver_efficient

/-- The verifier of the graph isomorphism protocol is a PPT strategy [PS10, Definition 116.1
for Proposition 120.7] (Inf-4.2).

**Proof sketch.** As `giProver_efficient`: the challenge is the first coin
(`polyTimeComputable_pairFstD`-style projection of one bit), the verdict compares
`polyTimeComputable_encPermGraph` on `⟨G_b, γ⟩` with `H` by `polyTimeComputable_pairEq`,
conjoined (`polyTimeComputable_and`) with the well-formedness test (`polyTimeComputable_lenEq`
against the squared vertex count in unary and `computesFunInTime_pairValid`). -/
theorem giVerifier_efficient : giVerifier.Efficient := GI.giVerifier_efficient

/-- The verifier of one iteration of the graph non-isomorphism protocol is a PPT strategy
[PS10, Proposition 118.4] (Inf-4.2): as `giVerifier_efficient`, with the first message
`polyTimeComputable_encPermGraph` on `⟨G_b, encPerm σ⟩` for `σ` from
`polyTimeComputable_encSamplePerm` and the verdict a one-bit comparison. -/
theorem gniVerifier_efficient : gniVerifier.Efficient := GI.gniVerifier_efficient

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy
(Inf-4.2): the coin block of iteration `hist.length` is cut by `pairTakePoly`/`pairDropPoly`
with the unary block length, the message as in `gniVerifier_efficient`, and the verdict is a
loop over the `|x|` replies (`polyTimeComputable_iterate` with an accumulated conjunction). -/
theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := GI.gniVerifierRep_efficient

/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2): as
`giProver_efficient` with the coin block of iteration `hist.length / 2` cut by
`pairTakePoly`/`pairDropPoly` and the parity test of the history length. -/
theorem giProverRep_efficient : giProverRep.Efficient := GI.giProverRep_efficient

/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2):
the challenge is coin `hist.length / 2`, and the verdict is a loop over the `|x|` pairs
`(H_j, γ_j)` of the history (`polyTimeComputable_iterate` over `polyTimeComputable_encPermGraph`
and `polyTimeComputable_pairEq`). -/
theorem giVerifierRep_efficient : giVerifierRep.Efficient := GI.giVerifierRep_efficient

/-! ### The propositions [PS10, Propositions 118.4 and 120.7] -/

/-- One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n` [PS10, Proposition 118.4, one
iteration] (Prop-118.4).

**Deviation (D10):** the verifier's `σ` is rejection-sampled; on a sampling failure `H = G_b`
may reveal `b`, whence the additional term `permFailBound n` with `n = instanceVertices |x|`.

**Proof sketch.** Completeness: for `x = encInstance G₀ G₁ ∈ L_niso` the verifier's message
decodes to `σ(G_b)` (`decGraphAt_encGraph`, `instanceVertexCount_encInstance`), the honest
reply is `b` by `gni_honest_reply`, and `wellFormedInstance x = true`, so the verdict is
`[true]` on every coin pair (`HardcoreBit.uprob_eq_one_of_forall`). Soundness: for
`x ∉ L_niso`, either `wellFormedInstance x = false` (verdict `[false]` always) or
`x = encInstance G₀ G₁` with `σ₀(G₀) = G₁` (`encInstance_mem_Lniso_iff`); fix the prover's
coins (`Protocol.exists_proverCoins_le`), split the verifier's tape into `b` and the sampler
bits (`uprob_prod` through the bijection `Fin (1 + c) → Bool ≃ Bool × (Fin c → Bool)`), and
bound `Pr[b' = b] ≤ Pr[b' = b ∧ sampler succeeds] + Pr[fail]`; on success the permutation is
uniform (`statClose_samplePerm`, `StatClose.abs_uprob_sub_le_prod`) and
`uprob_permGraph_eq_of_isomorphic` makes `H` independent of `b`, so the first term is
`≤ 1/2` (`uprob_bool_prod`); the second is `≤ permFailBound n` with
`n = instanceVertices |x|` (`instanceVertices_length_encInstance`). Efficiency:
`gniVerifier_efficient`. -/
theorem gni_interactiveProofErr :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) :=
  GI.gni_interactiveProofErr gniVerifier_efficient

/-- The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso`
[PS10, Proposition 118.4] (Prop-118.4).

**Deviation:** `|x|` iterations (soundness `2^{-|x|}`) plus the sampling term
`|x| · permFailBound n` (D10).

**Proof sketch.** Completeness as in `gni_interactiveProofErr`, iteration by iteration
(the history has exactly `|x|` replies, `exec_length`). Soundness with
`ε N := 2⁻¹ ^ N + N · permFailBound (instanceVertices N) + 2⁻¹ ^ N` (strict clause): fix the
prover's coins, condition on all `|x|` samplers succeeding (union bound `uprob_exists_le`
over the iterations, `statClose_samplePerm` per block via `pushesUniform_coinTable`), and
apply `uprob_gni_rep_cheat` (with `ρ := P'.Coins |x|`, a nonempty tape type) with `g_i := `
the prover's reply after the graphs `H_0, …, H_i` (the prover's `i`-th activation reads
exactly the graphs received so far, `exec_succ`).
Negligibility: `negligible_two_pow_neg`, `negligible_mul_permFailBound`, `Negligible.add`.
Efficiency: `gniVerifierRep_efficient`. -/
theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
  GI.gni_interactiveProof gniVerifierRep_efficient

/-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`
[PS10, Proposition 120.7, corrected: for `L_iso`, not `L_niso`] (Prop-120.7).

**Proof sketch.** Completeness for every witness: for `x = encInstance G₀ G₁`,
`y = encPerm σ` with `σ(G₀) = G₁`, the transcript is `[H, γ]` with `H = encGraph (π(G₀))` and
`γ = encPerm (if b then π σ⁻¹ else π)` (`exec_succ`, `decPerm_encPerm`), and the verdict is
`[true]` by `gi_honest_reply_eq`, `decGraph_encGraph`, `wellFormedInstance` on every coin
pair (`HardcoreBit.uprob_eq_one_of_forall`) — for every value of `π`, so the sampler's
failures are harmless. Completeness of `InteractiveProofErr` is the witness
`encPerm σ` of `Liso`. Soundness: for `x ∉ L_iso` either `x` is malformed (verdict `[false]`)
or `x = encInstance G₀ G₁` with `G₀ ≇ G₁` (`encInstance_mem_Liso_iff`); the verifier's tape is
one bit (`Fin 1 → Bool ≃ Bool`), so after `Protocol.exists_proverCoins_le`,
`uprob_gi_cheat_le_half` with `H r :=` the prover's first message decoded and
`γ b r :=` its reply to `[b]` decoded gives `Pr[accept] ≤ 1/2`, i.e. `1/2 ≤ Pr[out = [false]]`
(`uprob_not`). Efficiency: `giProver_efficient`, `giVerifier_efficient`. -/
theorem gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) :=
  GI.gi_efficientProverProofErr giProver_efficient giVerifier_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
efficient prover with respect to `R_iso` [PS10, Proposition 120.7, repeated] (Prop-120.7,
Lem-120.d).

**Deviation:** `|x|` iterations of four moves each (D8 fixed alternation).

**Proof sketch.** Completeness as in `gi_efficientProverProofErr` for each of the `|x|`
iterations (the verifier's history is `[H_0, γ_0, …]`, `exec_succ`, parity bookkeeping of
`giProverRep`/`giVerifierRep`). Soundness with `ε N := 2⁻¹ ^ N + 2⁻¹ ^ N` (strict clause): fix
the prover's coins; the verifier's tape is the challenge tuple `Fin |x| → Bool` (`List.ofFn`),
and `uprob_gi_rep_cheat_le` with `H_i` the decoded `i`-th graph message and `γ_i` the decoded
`i`-th reply (functions of the earlier challenges through `exec`) gives
`Pr[accept] ≤ 2^{-|x|}`; `negligible_two_pow_neg`. Efficiency: `giProverRep_efficient`,
`giVerifierRep_efficient`. -/
theorem gi_rep_efficientProverProof : EfficientProverProof giProtocolRep Liso Riso :=
  GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso`
[PS10, Proposition 120.7]. -/
theorem gi_rep_interactiveProof : InteractiveProof giProtocolRep Liso :=
  gi_rep_efficientProverProof.toInteractiveProof

end TCSlib.Cryptography
