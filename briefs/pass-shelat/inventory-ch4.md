# Inventory — [PS10] Chapter 4, *Knowledge* (§4.1–4.9)

Run 1 (understand & design) of the Pass–shelat Chapters 2–4 campaign. Source:
`blueprint/src/references/pass-shelat-2010-ch4.raw.md` (plus Appendix B,
`…-appendix.raw.md`, for witness relations). Results are cited as `[PS10, <page>.<counter>]`.

This file is the input of the statement-phase planners. Every item below is one Lean
declaration (or a tight cluster of declarations in one file). Items the chapter leaves
unnumbered carry page-letter ids (`Def-114.a`, `Claim-117.c`, …); campaign infrastructure
items specific to Chapter 4 carry `Inf-4.<k>` ids.

## 0. Reading guide and conventions

* **Two layers, as in the Garg campaign (plan D2).** Every protocol statement has a
  *concrete* form at one common input `x` (typed objects — graphs on `Fin n`, permutations,
  `Fin 3`-colourings; coins ranging over arbitrary finite types; all probabilities are
  `TCSlib.Cryptography.uprob` over the product of the coin types, all indistinguishability
  statements are `distAdv` bounds) and an *asymptotic* form (string common input, PPT /
  nuPPT machines of plan D3/D4, negligible functions of `|x|`). The chapter's mathematics
  lives entirely in the concrete layer; the asymptotic layer adds (i) string encodings
  (`Inf-4.1`), (ii) machine closure for the honest parties and simulators (`Inf-4.2`,
  `Inf-4.3`), (iii) the negligibility bookkeeping `2^{-n(x)}`, `e^{-n(x)}` versus `|x|`
  (`Inf-4.4`).
* **Interaction model (plan D8).** An interactive machine is a *next-message function*
  `(x, z, r, received) ↦ message` plus an output function of the final view; a protocol is a
  pair with a fixed polynomial number of rounds; executions are obtained by iterating the two
  functions; `view_A = (x, z_A, r_A, M_A)`, `transcript = (M_A, M_B)`, `out_A = A.out(view_A)`.
  No tapes, states or idle transitions are modelled (Deviation, recorded once in
  `Interaction.lean`).
* **Simulators are strict PPT (plan D8).** The two rewinding simulators (123.4, 128.7) are
  truncated at `n` resp. `n·|E|` attempts and output `⊥` on failure; the resulting theorems
  are *statistical* zero-knowledge with error `2^{-n}` (GI) and a computational bound with an
  additional `e^{-n}` term (3COL). The perfect-simulation lemma is proved as stated
  (conditioned on success). Expected polynomial time (Def-121.a) and the untruncated loop
  (Claim-123.a) are deferred.
* **Scope.** `core` = mandatory content of the plan; `optional` = feasible, nice to have;
  `deferred` = cited without proof in the text and used by nothing downstream, or outside
  the frozen model (expected PPT, §7.2.1 sequential composition, Shamir).
* **Difficulty** 1 (trivial) … 5 (research-level or large machine-building fill).

### Dependencies on the Chapter 2/3 inventories (ids as used there)

Def-23.4 (PPT), Def-23.5 (running time, worst case over coins), Def-24.6 (computes with
probability 1), Def-24.7 (private-key encryption scheme), Def-26.8 (nuPPT, advice form),
Def-27.2 (negligible), Def-27.3 (strong OWF; "one-way permutation" = length-preserving
bijective OWF, single-function reading as in Thm 79.4), Def-55.1 (OWP collection — *not* the
form used in §4.7), Def-69.3/69.4 (ensembles, `≈`), Lem-71.5 (closure under efficient
operations), Lem-71.6 (hybrid lemma), Lem-73.8 (prediction lemma), Def-78.3 (hard-core
predicate), Thm-87.3 (Goldreich–Levin, for the unconditional form of Thm-126.4), Def-91.1
(single-message secure encryption), Def-93.1 (multi-message security, the model for
Claim-126.a), Def-102.1/102.2 (PKE), Thm-104.4 (whose proof is reused verbatim for
Claim-127.c).

### Design questions the panel must settle (DQ)

* **DQ1 — exact uniform sampling of `S_n`, of an edge of `E`, of `S_3`.** With a worst-case
  bounded coin *string* (D3) a PPT cannot sample `σ ∈ S_n` exactly uniformly (`n! ∤ 2^ℓ`),
  nor an edge of `E` when `|E|` is not a power of two. Options: (A) keep D3 and prove
  near-uniform samplers with statistical error `≤ 2^{-n}` at the machine level (every bound
  of the chapter gains a `2^{-n}` term; a large machine-building task); (B) let honest
  strategies and simulators draw their coins uniformly from a *finite type* `ρ n` whose
  elements have polynomial-length encodings, the next-message machine reading the encoding
  (D3 is the special case `ρ n = Fin ℓ → Bool`). Adversaries (`V*`, `P*`, `D`) keep D3/D4.
  Recommendation: (B), recorded as a Deviation; the concrete layer is written over arbitrary
  finite coin types either way, so the choice only affects `Inf-4.2`.
* **DQ2 — typed common inputs.** Concrete-layer protocols take typed common inputs
  (`SimpleGraph (Fin n) × SimpleGraph (Fin n)`, `SimpleGraph (Fin n)`); the asymptotic
  definitions (116.1, 121.1, 121.2) are over `List Bool` and are instantiated through the
  adjacency-matrix encoding and total decoding with defaults (`Inf-4.1`).
* **DQ3 — Theorem 124.1 needs Levin (witness-preserving) reductions**, which neither
  the text's Appendix B nor the repository (`Complexity.NPHard` is Karp-only;
  `SATtoColor.SATtoColorReduction` is graph-level, with the colouring witness `private`)
  provides. Core form: ZK for every `(L, R_L)` that Levin-reduces to 3COL
  (Thm-124.1 + Claim-124.d); the "every language in NP" form takes string-level Levin
  NP-hardness of 3COL as a hypothesis (Claim-124.b/124.c deferred).
* **DQ4 — commitment security parameter.** Def 126.3 infers `n` from `|v|`; Protocol 127.5
  commits to 2-bit colours. The formal `Com` takes `n` explicitly and the colour is padded to
  `n` bits (Deviation; see Prot-127.5).
* **DQ5 — sequential repetition.** The text proves ZK for *one* iteration and defers the
  `n`-fold / `n|E|`-fold protocols to §7.2.1 (Claim-123.c, outside Chapters 2–4). Core
  theorems are stated for the single-iteration protocols (soundness error `1/2` resp.
  `1 − 1/|E|`) *and* for the repeated protocols' completeness/soundness; the repeated
  protocols' ZK is stated with Claim-123.c as an explicit hypothesis or left sorried under a
  sketch (deferred).

## 1. Existing Lean the chapter builds on (verified by `lake env lean` on 2026-10-27)

| Declaration (fully qualified) | File | Use in Chapter 4 |
| --- | --- | --- |
| `TCSlib.Cryptography.uprob`, `uexp`, `uprob_prod`, `uprob_comp_equiv`, `uprob_fst`, `uprob_mono`, `uprob_or_le`, `uprob_exists_le`, `uprob_eq_card_filter` | `TCSlib/Cryptography/Foundations/Probability.lean` | all probability statements |
| `TCSlib.Cryptography.abs_sub_le_sum_hybrids`, `exists_hybrid_gap`, `half_le_uprob_good` | same | hybrids in 112.2(ii), 126.a, 127.d, 129.d |
| `TCSlib.Cryptography.acceptProb`, `distAdv`, `predProb`, `acceptProb_comp_equiv`, `distAdv_le_statDist` | `Foundations/Experiments.lean` | ZK/hiding advantages; statistical ZK ⇒ computational |
| `TCSlib.Cryptography.Negligible`, `.add`, `.mul_pow`, `.const_mul`, `.mono`, `negligible_two_pow_neg`, `not_negligible_iff` | `Foundations/Negligible.lean` | every asymptotic statement |
| `TCSlib.Cryptography.uprob_eq_of_equiv`, `acceptProb_fst`, `acceptProb_snd`, `acceptProb_bind`, `acceptProb_update`, `pushSampler`, `sunglassRed`, `distAdv_sunglassRed`, `distAdv_comp`, `mixDist`, `distAdv_mixDist_eq`, `copies`, `multicopyRed`, `exists_multicopyRed_ge`, `distAdv_multicopyAvgRed` | `Pseudorandom/Indistinguishability.lean` | closure (Lem-71.5) and multi-copy hybrids (Claim-126.a, 127.d, 129.d) |
| `TCSlib.Cryptography.owpGen`, `owpGenNot`, `owpPair`, `owpPredictor`, `uprob_bool_prod`, `predProb_owpPredictor_false`, `predProb_owpPredictor_true`, `exists_owpPredictor` | `Pseudorandom/GeneratorFromPermutation.lean` | **exact** concrete content of commitment hiding (Claim-127.c) with `β := Unit` |
| `TCSlib.Cryptography.PushesUniform`, `pushesUniform_equiv`, `uprob_eq_one_of_forall`, `forall_of_uprob_eq_one`, `uprob_prod_and` | `HardcoreBit/Basic.lean` | uniform-permutation invariance (Lem-119.a), probability-1 completeness |
| `TCSlib.Cryptography.OneWay.uprob_pi_forall`, `uprob_eq_one_div_card`, `uprob_and_le_mul`, `uprob_congr` | `OneWayFunctions/Basic.lean` | counting lemmas Lem-119.c, Lem-127.g |
| `TCSlib.InformationTheory.statDist`, `statDist_triangle`, `FinDist.map`, `FinDist.uniform` | `TCSlib/InformationTheory/{StatisticalDistance,FinDist}.lean` | statistical ZK (Def-122.a, Thm-122.3.trunc, Claim-129.c) |
| `Schnorr.Transcript`, `honest`, `simulate`, `reindex`, `schnorr_completeness`, `schnorr_soundness`, `schnorr_hvzk` | `TCSlib/Cryptography/SchnorrProtocol.lean` | template (not reusable code): 3-move sigma protocol, HVZK by bijective reindexing = Thm-122.3.hv |
| `Complexity.NP`, `Complexity.mem_NP_iff_exists_length_le`, `Complexity.P_subset_NP` | `TCSlib/Complexity/ClassNP/NP.lean` | Def-191.11, Claim-117.c, Claim-118.b |
| `Complexity.P`, `Complexity.mem_P_iff`, `Complexity.DTIME` | `ClassP/{P,DTIME}.lean` | verifier predicates in `P` |
| `Complexity.PolyTimeReducible` (`≤ₚ`), `NPHard`, `NPComplete`, `mem_P_of_polyTimeReducible` | `ClassNP/Reductions.lean` | Karp reductions (Def-124.a extends to Levin) |
| `Complexity.PolyTimeComputable`, `.comp`, `.pairEncode`, `polyTimeComputable_ite`, `pairFstD`, `pairSndD`, `polyTimeComputable_lenEq` | `ClassNP/{PolyTime,PolyTimePairing}.lean` | machine-level PPT-ness of honest strategies (Inf-4.2) |
| `Complexity.SAT3`, `Complexity.SAT3_NPComplete` | `ClassNP/SAT.lean`, `CookLevin/Hardness.lean` | Claim-124.b |
| `Complexity.coNP` | `ClassNP/CoNP.lean` | Claim-118.c |
| `SATtoColor.Is3Colorable`, `ReductionGraph`, `SATtoColorReduction`, `SATtoColorCompleteness`, `Sat3` (`sat3Coloring` is `private`) | `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean` | Def-124.f, Claim-124.b/c |
| `Turing.FinTM`, `FinTM.ComputesInTime`, `ComputesFunInTime` | `TCSlib/Complexity/TuringMachine/Finite.lean` | machine layer |
| `Turing.pairEncode`, `pairDecode`, `pairDecode_pairEncode` | `TuringMachine/Encoding.lean` | encodings of views/messages (Inf-4.1) |
| `Turing.FinTM.DecidesWithAdviceInTime`, `DTIMEAdvice`, `PAdvicePoly` | `CircuitComplexity/Advice.lean` | nuPPT distinguishers (D4) |
| `Turing.FinTM.exists_loopFindTM`, `exists_loopTM`, `exists_emitLoopTM` | `TuringMachine/Build/Loop.lean` | truncated simulators as machines (Inf-4.3, via plan's `Randomized/Repetition.lean`) |
| Mathlib `SimpleGraph.Iso` (`≃g`), `SimpleGraph.Iso.map`, `SimpleGraph.map`, `map_map`, `map_id`, `map_symm`, `comap_symm`, `map_adj` | `Mathlib/Combinatorics/SimpleGraph/Maps.lean` | `σ(G)`, isomorphism (Def-117.e) |
| Mathlib `SimpleGraph.Coloring`, `Colorable`, `Coloring.mk`, `Coloring.valid`, `instance Fintype (Coloring G α)` | `Mathlib/Combinatorics/SimpleGraph/Coloring.lean` | 3COL (Def-124.f) |
| Mathlib `SimpleGraph.edgeFinset`, `mem_edgeFinset`, `fintypeEdgeSet`, `instance Fintype (SimpleGraph V)` (Basic.lean:110) | `Mathlib/Combinatorics/SimpleGraph/{Finite,Basic}.lean` | random edge of `E`, finiteness of graphs |
| Mathlib `Equiv.Perm`, `Fintype (Perm α)` (`Equiv.instFintype`/`fintypePerm`), `Fintype.card_perm`, `Equiv.mulRight` | `Mathlib/Data/Fintype/Perm.lean`, `Mathlib/Algebra/Group/…` | uniform permutations, `S_3` pair lemma |
| Mathlib `Real.add_one_le_exp`, `Real.one_sub_div_pow_le_exp_neg` | `Mathlib/Analysis/Complex/Exponential.lean` | Claim-125.a |

Nothing in the repository formalizes interaction, views, simulators, commitments, graph
isomorphism as a language, or the `3COL` language; `TCSlib/Cryptography/MPC/BGW/Privacy.lean`
(`linear_perfectPrivacy`: a bijection of the dealer's coins fixing a coalition's view) is the
closest "perfect simulation by reindexing" precedent and is a model for Claim-123.b.

## 2. Inventory table

Columns: id · kind · title · scope · difficulty · proposed file (under
`TCSlib/Cryptography/ZeroKnowledge/` unless absolute) · existing Lean (short) · depends on.

| id | kind | title | scope | diff | file | existing Lean | depends on |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Def-111.1 | Definition | Zero-knowledge (private-key) encryption | core | 2 | Encryption.lean | `distAdv`, `acceptProb`, `Negligible` | Def-24.7, Def-23.4, Def-26.8, Def-27.2 |
| Def-111.a | Definition | Perfect zero-knowledge encryption | optional | 1 | Encryption.lean | `FinDist.map`, `statDist` | Def-111.1 |
| Def-111.b | Definition | Zero-knowledge public-key encryption | optional | 2 | Encryption.lean | `distAdv` | Def-102.1 |
| Thm-112.2 | Theorem | Secure ⇔ zero-knowledge (private key) | core | 2 | Encryption.lean | — | Thm-112.2.i, Thm-112.2.ii |
| Thm-112.2.i | Theorem | Security ⇒ zero-knowledge | core | 2 | Encryption.lean | `distAdv` (sampler equality), PPT closure | Def-91.1, Def-111.1, Def-24.6 |
| Thm-112.2.ii | Theorem | Zero-knowledge ⇒ security | core | 1 | Encryption.lean | `abs_sub_le`, `Negligible.const_mul` | Def-91.1, Def-111.1 |
| Claim-112.a | Claim | The equivalence for public-key encryption | optional | 2 | Encryption.lean | as 112.2 | Def-102.2, Def-111.b |
| Claim-112.b | Claim | Perfect ZK encryption ⇔ perfect secrecy | optional | 1 | Encryption.lean | `FinDist.map` | Def-111.a |
| Def-114.a | Definition | Interactive machine as a next-message strategy | core | 2 | Interaction.lean | — (new model) | Def-23.4 |
| Def-114.b | Definition | Protocol (pair of strategies, round order, round bound) | core | 1 | Interaction.lean | — | Def-114.a |
| Def-115.a | Definition | Execution `A_{r1}(x,z1) ↔ B_{r2}(x,z2)` | core | 2 | Interaction.lean | — | Def-114.b |
| Def-115.b | Definition | Views `view_A`, `view_B`, joint view | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.c | Definition | Transcript | core | 1 | Interaction.lean | — | Def-115.a |
| Def-115.d | Definition | Outputs `out_X(e)`, `out(v)` | core | 1 | Interaction.lean | — | Def-115.b |
| Def-116.a | Definition | Random executions (samplers from the coin product) | core | 1 | Interaction.lean | `uprob`, `uprob_prod`, `acceptProb` | Def-115.a |
| Def-116.b | Definition | Time complexity of an ITM; PPT strategies | core | 3 | Interaction.lean | plan `Randomized/PPT.lean`, `pairEncode`, `FinTM.ComputesInTime` | Def-23.5, Def-114.a |
| Def-116.1 | Definition | Interactive proof system | core | 2 | InteractiveProofs.lean | `uprob`, `Negligible` | Def-116.b, Def-115.d, Def-116.a |
| Def-117.a | Definition | Soundness error `s(n)`; constant-error proofs | core | 1 | InteractiveProofs.lean | — | Def-116.1 |
| Def-117.b | Definition | The class `IP` | optional | 1 | InteractiveProofs.lean | `Language Bool` | Def-116.1 |
| Claim-117.c | Claim | `NP ⊆ IP` (send the certificate) | optional | 3 | InteractiveProofs.lean | `Complexity.NP`, `mem_P_iff` | Def-116.1, Def-191.11, Inf-4.2 |
| Claim-117.d | Claim | `IP = PSPACE` (Shamir, cited) | deferred | 5 | — | — | Def-117.b |
| Def-117.e | Definition | Graphs on `Fin n`, `σ(G)`, isomorphism via permutations | core | 2 | GraphIsomorphism.lean | `SimpleGraph.map`, `Iso.map`, `map_map`, `map_id`, `map_symm`, `Equiv.Perm` | — |
| Def-118.a | Definition | `L_iso`, `L_niso`, witness relation `R_iso` | core | 2 | GraphIsomorphism.lean | `SimpleGraph.Iso` | Def-117.e, Inf-4.1 |
| Claim-118.b | Claim | `L_iso ∈ NP` (string level) | optional | 4 | GraphIsomorphism.lean | `Complexity.NP`, `mem_NP_iff_exists_length_le` | Def-118.a, Inf-4.1 |
| Claim-118.c | Claim | `L_niso ∈ coNP` | deferred | 4 | GraphIsomorphism.lean | `Complexity.coNP` | Claim-118.b |
| Prot-118.3 | Protocol | Graph non-isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `Fintype (Perm α)` | Def-114.b, Def-117.e |
| Lem-119.a | Lemma | Uniformly permuted isomorphic graphs are identically distributed | core | 2 | GraphIsomorphism.lean | `uprob_comp_equiv`, `pushesUniform_equiv`, `Equiv.mulRight` | Def-117.e |
| Lem-119.b | Lemma | `n`-fold GNI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod`, `uprob_eq_of_equiv` | Lem-119.a, Lem-119.c |
| Lem-119.c | Lemma | Adaptive guessing lemma `Pr[∀i, b_i = g_i(b_{<i}, w)] = 2^{-n}` | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_div_card`, `uprob_prod` | — |
| Lem-119.d | Lemma | GNI completeness (unbounded prover, probability 1) | core | 2 | GraphIsomorphism.lean | `uprob_eq_one_of_forall` | Prot-118.3, Lem-120.b |
| Prop-118.4 | Proposition | Protocol 118.3 is an interactive proof for `L_niso` | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-119.b, Lem-119.d, Def-116.1, Inf-4.2, Inf-4.4 |
| Def-119.5 | Definition | Interactive proof with efficient prover w.r.t. `R_L` | core | 2 | InteractiveProofs.lean | — | Def-116.1, Def-191.11 |
| Def-119.e | Definition | Interactive argument (nuPPT cheating provers) | optional | 2 | InteractiveProofs.lean | `DecidesWithAdviceInTime` (D4) | Def-116.1, Def-26.8 |
| Claim-119.f | Claim | Poly-time GNI prover would put `L_niso` in NP (informal) | deferred | 4 | — | — | Claim-118.c |
| Prot-120.6 | Protocol | Graph isomorphism protocol (single and `n`-fold) | core | 2 | GraphIsomorphism.lean | `Equiv.Perm`, `SimpleGraph.map` | Def-114.b, Def-118.a |
| Lem-120.a | Lemma | Completeness algebra `π(G0) = H`, `(π∘σ⁻¹)(G1) = H` | core | 1 | GraphIsomorphism.lean | `map_map`, `map_symm` | Def-117.e |
| Lem-120.b | Lemma | A graph is isomorphic to at most one of two non-isomorphic graphs | core | 1 | GraphIsomorphism.lean | `map_map` | Def-117.e |
| Lem-120.c | Lemma | Single-iteration GI soundness `≤ 1/2` | core | 2 | GraphIsomorphism.lean | `uprob_prod`, `uprob_bool_prod` | Lem-120.b |
| Lem-120.d | Lemma | `n`-fold GI soundness `≤ 2^{-n}` against adaptive provers | core | 3 | GraphIsomorphism.lean | `uprob_prod` | Lem-119.c, Lem-120.b |
| Prop-120.7 | Proposition | Protocol 120.6 is an interactive proof for `L_iso` with efficient prover | core | 3 | GraphIsomorphism.lean | `negligible_two_pow_neg` | Lem-120.a, Lem-120.d, Def-119.5, Inf-4.2, Inf-4.4 |
| Def-121.1 | Definition | Honest-verifier zero-knowledge | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-119.5, Def-115.b, Def-26.8 |
| Def-121.2 | Definition | Zero-knowledge (every PPT `V*`) | core | 2 | Defs.lean | `distAdv`, `Negligible` | Def-121.1, Def-116.b |
| Def-121.a | Definition | Expected polynomial time | deferred | 4 | — | `uexp` | Def-23.5 |
| Def-122.a | Definition | Perfect and statistical zero-knowledge | core | 2 | Defs.lean | `statDist`, `distAdv_le_statDist` | Def-121.2 |
| Claim-122.b | Claim | View-based ZK ⇔ output-based ZK (exercise) | optional | 3 | Defs.lean | `distAdv_sunglassRed` | Def-121.2, Lem-71.5 |
| Claim-122.c | Claim | ZK against PPT `V*` with auxiliary input covers nuPPT `V*` | deferred | 3 | — | — | Def-121.2, Def-26.8 |
| Thm-122.3 | Theorem | Protocol 120.6 is a (statistical, single-iteration) ZK proof for `L_iso` | core | 4 | GraphIsomorphismZK.lean | `distAdv_le_statDist`, `negligible_two_pow_neg` | Prop-120.7, Thm-122.3.trunc, Claim-123.d, Claim-123.c |
| Thm-122.3.hv | Theorem | Honest-verifier perfect ZK of one GI iteration by reindexing | core | 2 | GraphIsomorphismZK.lean | `Schnorr.schnorr_hvzk` (template), `acceptProb_comp_equiv` | Prot-120.6, Lem-120.a, Def-121.1 |
| Thm-122.3.trunc | Theorem | Truncated simulator: `Pr[⊥] = 2^{-n}`, `statDist ≤ 2^{-n}` | core | 4 | GraphIsomorphismZK.lean | `uprob_prod`, `statDist`, `distAdv_le_statDist` | Alg-123.4, Lem-123.5, Claim-123.b |
| Alg-123.4 | Algorithm | Simulator for GI (truncated at `n` attempts) | core | 3 | GraphIsomorphismZK.lean | `Fintype (Perm α)` | Prot-120.6, Def-114.a |
| Lem-123.5 | Lemma | `H ~ π(G0)` independent of `b'`; `Pr[b = b'] = 1/2` | core | 2 | GraphIsomorphismZK.lean | `uprob_bool_prod`, `uprob_prod`, `uprob_comp_equiv` | Lem-119.a, Alg-123.4 |
| Claim-123.a | Claim | Untruncated simulator has expected 2 trials | deferred | 3 | — | `uexp` | Def-121.a, Lem-123.5 |
| Claim-123.b | Claim | Perfect simulation conditioned on success | core | 4 | GraphIsomorphismZK.lean | `uprob_eq_of_equiv`, BGW `linear_perfectPrivacy` (precedent) | Lem-123.5, Lem-120.a |
| Claim-123.c | Claim | Sequential repetition preserves ZK (§7.2.1) | deferred | 5 | — | — | Def-121.2 |
| Claim-123.d | Claim | Truncated GI simulator is strict PPT | core | 4 | GraphIsomorphismZK.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-123.4 |
| Thm-124.1 | Theorem | OWP ⇒ ZK proofs for NP (Levin-reducible form) | core | 4 | NP.lean | `Complexity.NP`, `PolyTimeReducible` | Thm-126.4, Prop-127.6, Claim-124.d, Def-124.a |
| Def-124.a | Definition | Levin (witness-preserving) reduction | core | 2 | NP.lean | `PolyTimeReducible`, `PolyTimeComputable` | Def-191.11 |
| Claim-124.b | Claim | 3COL is NP-complete at the string level | deferred | 5 | NP.lean | `SAT3_NPComplete`, `SATtoColorReduction` | Inf-4.1 |
| Claim-124.c | Claim | Witness transformation 3SAT → 3COL (`sat3Coloring`) | deferred | 4 | NP.lean | `SATtoColorCompleteness` (private `sat3Coloring`) | Claim-124.b |
| Claim-124.d | Claim | ZK proofs are preserved under Levin reductions | core | 3 | NP.lean | — | Def-124.a, Def-121.2, Def-119.5 |
| Claim-124.e | Claim | One-way functions suffice (cited) | deferred | 5 | — | — | Thm-124.1 |
| Def-124.f | Definition | The language 3COL and its witness relation (typed) | core | 1 | ThreeColoring.lean | `SimpleGraph.Colorable`, `Coloring`, `SATtoColor.Is3Colorable` | — |
| Claim-125.a | Claim | `(1 − 1/m)^{n·m} ≤ e^{-n}` (soundness after `n·|E|` rounds) | core | 1 | ThreeColoring.lean | `Real.one_sub_div_pow_le_exp_neg`, `Real.add_one_le_exp` | — |
| Def-126.3 | Definition | Commitment scheme (binding, hiding) | core | 2 | Commitment.lean | `distAdv`, `Negligible`, `PolyTimeComputable` | Def-26.8, Def-27.2 |
| Claim-126.a | Claim | Every commitment scheme is multi-value hiding | core | 3 | Commitment.lean | `exists_hybrid_gap`, `mixDist`, `exists_multicopyRed_ge` (generalize) | Def-126.3, Lem-71.6 |
| Thm-126.4 | Theorem | OWP (with hard-core predicate) ⇒ commitment schemes | core | 3 | Commitment.lean | `exists_owpPredictor` | Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d, Def-78.3, Thm-87.3 |
| Alg-127.a | Construction | `Com(b,r) = (f(r), b ⊕ h(r))`; bitwise `n`-bit scheme | core | 1 | Commitment.lean | `owpGen`, `owpGenNot` (`β := Unit`) | Def-27.3, Def-78.3 |
| Claim-127.b | Claim | Binding of Alg-127.a | core | 1 | Commitment.lean | `Equiv.injective` | Alg-127.a |
| Claim-127.c | Claim | Hiding of the single-bit scheme = predictor reduction | core | 2 | Commitment.lean | `predProb_owpPredictor_false/true`, `exists_owpPredictor` | Alg-127.a, Def-78.3, Lem-73.8 |
| Claim-127.d | Claim | Bitwise scheme hiding by hybrid ("show this!") | core | 3 | Commitment.lean | `exists_hybrid_gap`, `acceptProb_update`, `Negligible.mul_pow` | Claim-127.c, Lem-71.6 |
| Prot-127.5 | Protocol | ZK protocol for 3-colouring (single and `n·|E|`-fold) | core | 3 | ThreeColoring.lean | `edgeFinset`, `Fintype (Perm (Fin 3))` | Def-126.3, Def-124.f, Def-114.b |
| Claim-127.e | Claim | Completeness of Protocol 127.5 | core | 1 | ThreeColoring.lean | `Coloring.valid`, `uprob_eq_one_of_forall` | Prot-127.5 |
| Lem-127.f | Lemma | Committed colouring from binding; a bad edge exists | core | 2 | ThreeColoring.lean | — | Def-126.3, Def-124.f |
| Lem-127.g | Lemma | Adaptive sequential soundness with escape probability `1/m` | core | 3 | ThreeColoring.lean | `uprob_prod`, `uprob_and_le_mul` | Lem-119.c (model) |
| Claim-127.h | Claim | Soundness of Protocol 127.5: `≤ (1−1/|E|)^{n|E|} ≤ e^{-n}` | core | 3 | ThreeColoring.lean | — | Lem-127.f, Lem-127.g, Claim-125.a |
| Prop-127.6 | Proposition | Protocol 127.5 is a ZK proof for 3COL | core | 4 | ThreeColoring.lean | — | Claim-127.e, Claim-127.h, Prop-128.8, Inf-4.2, Inf-4.4, Claim-123.c |
| Alg-128.7 | Algorithm | Simulator for 3-colouring (truncated at `n·|E|` attempts) | core | 3 | ThreeColoring.lean | — | Prot-127.5, Def-114.a |
| Claim-128.a | Claim | The 3COL simulator is strict PPT | core | 4 | ThreeColoring.lean | `exists_loopFindTM` via `Randomized/Repetition` | Inf-4.3, Alg-128.7 |
| Prop-128.8 | Proposition | ZK of the 3COL simulator (computational) | core | 5 | ThreeColoring.lean | `abs_sub_le`, `distAdv_le_statDist`, `Negligible.add` | Claim-129.a, Claim-129.c, Claim-129.d |
| Claim-129.a | Claim | `S ≡ S'` (random distinct pair = permuted witness colours) | core | 2 | ThreeColoring.lean | `uprob_comp_equiv` | Lem-129.b, Alg-128.7 |
| Lem-129.b | Lemma | `π ↦ (π a, π b)` is a bijection `S_3 ≃ {(u,v) ∣ u ≠ v}` | core | 2 | ThreeColoring.lean | `Fintype.card_perm`, `decide` | — |
| Claim-129.c | Claim | `S''` fails w.p. `(1−1/|E|)^{n|E|}` and is perfect given success | core | 4 | ThreeColoring.lean | `uprob_prod`, `statDist` | Alg-128.7, Claim-123.b (model) |
| Claim-129.d | Claim | `S' ≈ S''` by hybrids over attempts and multi-value hiding | core | 5 | ThreeColoring.lean | `exists_hybrid_gap`, `distAdv_sunglassRed`, `mixDist`, `Negligible.mul_pow` | Claim-126.a, Lem-71.5, Lem-71.6 |
| Def-191.10 | Definition | `DP` (deterministic polynomial time) | optional | 1 | `TCSlib/Complexity/ClassP/P.lean` (exists) | `Complexity.P` | — |
| Def-191.11 | Definition | NP via witness relations, `R_L(x)` | core | 1 | InteractiveProofs.lean (typed) / `ClassNP/NP.lean` (exists) | `Complexity.NP`, `mem_NP_iff_exists_length_le` | — |
| Def-192.12 | Definition | `BPP` | optional | 2 | plan `Randomized/PPT.lean` | — | Def-23.4 |
| Inf-4.1 | Infrastructure | String encodings of graphs, permutations, colourings, messages, views | core | 4 | Encoding.lean (new) | `pairEncode`, `pairFstD`, `PolyTimeComputable.pairEncode` | — |
| Inf-4.2 | Infrastructure | Machine-level PPT-ness of honest parties; sampling (DQ1) | core | 5/3 | Encoding.lean + protocol files | `PolyTimeComputable.*`, `polyTimeComputable_ite` | Inf-4.1, Def-116.b |
| Inf-4.3 | Infrastructure | Restart loops with a bounded number of attempts as strict PPT | core | 4 | plan `TCSlib/Complexity/Randomized/Repetition.lean` | `exists_loopFindTM` | Def-116.b |
| Inf-4.4 | Infrastructure | `2^{-n(x)}`, `e^{-n(x)}` negligible in `|x|` when `n(x) ≥ √(|x|/C)` | core | 2 | Defs.lean | `negligible_two_pow_neg`, `Negligible.mono` | — |

## 3. Statements, reuse notes, text issues (one entry per item)

### §4.2 Zero-knowledge encryption — `ZeroKnowledge/Encryption.lean`

**Def-111.1 (ZK encryption).** A private-key scheme `(Gen, Enc, Dec)` [Def-24.7] is
zero-knowledge if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `n` ∀ `m ∈ {0,1}^n`:
`|Pr[k ← Gen(1^n); c ← Enc_k(m) : D(c) = 1] − Pr[c ← S(1^n) : D(c) = 1]| ≤ ε(n)`.
Concrete layer at `n`: samplers `encS n m : ρ_G n × ρ_E n → C n`, `S n : ρ_S n → C n`,
bound `distAdv (encS n m) (S n) (D n) ≤ ε n`. *Reuse:* `distAdv` is exactly the
quantity; the asymptotic wrapper quantifies `S` over PPT samplers and `D` over nuPPT
distinguishers of the ensemble layer. *Note:* the message `m` is fixed per `n` (no
adversarial message ensemble beyond "∀ m"); `S` gets `1^n` only.

**Def-111.a (perfect ZK encryption).** As Def-111.1 with the two distributions identical:
`FinDist.map (encS n m) uniform = FinDist.map (S n) uniform` for all `n, m` (equivalently
`distAdv … D = 0` for every `D`, even unbounded).

**Def-111.b (ZK PKE).** `(Gen, Enc, Dec)` [Def-102.1] is ZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negl
`ε` ∀ `n`, `m ∈ {0,1}^n`: `D` distinguishes `{(pk,sk) ← Gen(1^n) : (pk, Enc_pk(m))}` and
`{(pk,sk) ← Gen(1^n) : (pk, S(pk, 1^n))}` with advantage `≤ ε(n)`. Note the simulator is
given `pk` and the distinguisher sees `pk`.

**Thm-112.2.** Hypotheses: `Gen`, `Enc` PPT; a deterministic polynomial-time `M` with
`M(1^n) ∈ {0,1}^n` for every `n`. Conclusion: Def-91.1 ⇔ Def-111.1. Split:

* **Thm-112.2.i (secure ⇒ ZK).** Take `S(1^n) := Enc_k(M(1^n))` with `k ← Gen(1^n)`,
  coins `(g, e)`. For every `D`, `n`, `m`: the sampler of `S(1^n)` *is* the sampler of
  `Enc_k(M(1^n))`, so `distAdv (encS n m) (S n) D = distAdv (encS n m) (encS n (M n)) D ≤ ε_D(n)`
  by Def-91.1 with `m0 := m`, `m1 := M(1^n)`. Concrete content: definitional equality of
  samplers. Asymptotic bridge: `S` is PPT by closure (composition of `M`, `Gen`, `Enc`;
  plan `Randomized/Closure.lean`). *Text issue:* the proof by contradiction via "infinitely
  many `n`" is unnecessary; also `M(1^n)` must be deterministic for the sampler identity
  (a randomized `M` would still work via averaging over its coins).
* **Thm-112.2.ii (ZK ⇒ secure).** For all `D`, `n`, `m1`, `m2`:
  `distAdv (encS n m1) (encS n m2) D ≤ distAdv (encS n m1) (S n) D + distAdv (S n) (encS n m2) D ≤ 2 ε(n)`
  (triangle inequality `abs_sub_le`, then `Negligible.const_mul`). The text's "hybrid
  lemma with `1/(2p(n))`" is this two-step chain.

**Claim-112.a.** The same equivalence for PKE (Def-102.2 ⇔ Def-111.b) with
`S(pk, 1^n) := Enc_pk(M(1^n))`; identical proof (the point: encryption under `pk` is
publicly samplable). Optional.

**Claim-112.b.** Perfect ZK encryption ⇔ perfect secrecy (`Enc_k(m) ≡ Enc_k(m')` for all
`m, m'` at every `n`): `S := Enc_k(m_0)` for the fixed message `m_0 = M(1^n)`, both
directions are rewriting of distribution equalities. Perfect secrecy is a Chapter 1 notion;
state the concrete form only. Optional.

### §4.4 Interactive protocols — `ZeroKnowledge/Interaction.lean`

**Def-114.a (ITM as a strategy).** Concrete form, parametrized by a common-input type `X`,
auxiliary-input type `Z`, a finite coin type `ρ`, and a message type `Msg`:
`next : X → Z → ρ → List Msg → Msg` (the message sent after having *received* the listed
messages) and `out : X → Z → ρ → List Msg → Out`. String form: `X = Z = Msg = Out = List Bool`,
`ρ = Fin ℓ → Bool`. Deviation (D8): no tapes/states; "entering the idle state" is returning
from `next`; halting is handled by the protocol's round bound. The honest prover's witness
is its auxiliary input `z`.

**Def-114.b (protocol).** `Protocol A B := (A : Strategy …, B : Strategy …, first : Bool,
rounds : ℕ)`; in round `i` the active party is `A` iff `i` has the parity of `first`. All
protocols of the chapter have fixed round counts (GNI: 2 rounds per iteration, `V` first;
GI and 3COL: 3 rounds per iteration, `P` first).

**Def-115.a (execution).** For `x, z1, z2, r1, r2`, the pair
`((x, z1, r1, M_A), (x, z2, r2, M_B))` where `M_A` (resp. `M_B`) is the list of messages
received by `A` (resp. `B`), defined by structural recursion on the round index:
the sender's message in round `i` is its `next` applied to its received messages so far.
Notation `A_{r1}(x,z1) ↔ B_{r2}(x,z2)`. Lean: `exec P x z1 z2 r1 r2 : View × View`,
with `View := X × Z × ρ × List Msg` (typed per party).

**Def-115.b (views).** `viewA := (exec …).1`, `viewB := (exec …).2`; the execution itself is
the joint view.

**Def-115.c (transcript).** `(M_A, M_B)` of an execution (projection).

**Def-115.d (outputs).** `out_X(e) := X.out (view_X e)`; `out(v) := X.out v` for a view `v`
of `X`. For verifiers `Out = Bool` (accept).

**Def-116.a (random executions).** The distribution `A(x,z1) ↔ B(x,z2)` is the sampler
`(r1, r2) ↦ exec … r1 r2` on the uniform product `ρ_A × ρ_B`; `view`, `out` distributions
are its post-compositions. Plugs directly into `uprob`, `acceptProb`, `distAdv`
(`uprob_prod` for conditioning on one party's coins). No new content.

**Def-116.b (time complexity, PPT strategy).** `A` has time complexity `t` if for every
`B`, `x`, `z_a`, `z_b` and all coins, `A(x, z_a)` halts within `t(|x|)` steps in the
interaction. Formal: a strategy is PPT if there are `C, c, R` and a `FinTM Bool` computing
`next` (and `out`) on `pairEncode x (pairEncode z (pairEncode (enc r) (encodeList received)))`
within `C·(|x|+1)^c` steps *for every* `z`, `r`, `received` (bound in `|x|` only, as in the
text; the machine cannot read more than `C(|x|+1)^c` bits of `z`), coins of length
`C_r·(|x|+1)^{c_r}` (or a typed coin space per DQ1), and at most `R(|x|)` rounds. Deviation:
per-message bound instead of a total bound (total `≤ R·t`). Depends on the frozen
`Randomized/PPT.lean` signatures.

### §4.5 Interactive proofs — `ZeroKnowledge/InteractiveProofs.lean`, `GraphIsomorphism.lean`

**Def-116.1 (interactive proof).** `(P, V)` is an interactive proof system for `L` if `V` is
PPT (Def-116.b) and (1) completeness: ∀ `x ∈ L` ∃ `y` ∀ `z`:
`Pr_{r_P, r_V}[out_V[P_{r_P}(x,y) ↔ V_{r_V}(x,z)] = 1] = 1`; (2) soundness: ∃ negligible `ε`
∀ `x ∉ L` ∀ strategies `P*` (arbitrary function, arbitrary finite coin type, *no* auxiliary
input) ∀ `z`: `Pr[out_V[P*(x) ↔ V(x,z)] = 0] > 1 − ε(|x|)`. Formalized with
`Pr[out_V = 1] ≤ ε(|x|)` (equivalent up to the strictness of the inequality, immaterial for
negligible `ε`; `out_V : Bool`). The quantification over `P*` with an arbitrary coin type is
universe-polymorphic; use coin strings `Fin ℓ → Bool` for arbitrary `ℓ` (WLOG deterministic
`P*` by averaging — record as a lemma). *Text issue:* "`> 1 − e`" strict.

**Def-117.a (soundness error).** Same with `1 − ε(|x|)` replaced by `1 − s(|x|)` for a given
`s : ℕ → ℝ` (e.g. constant `1/2`). Used for the single-iteration protocols.

**Def-117.b (IP).** `IP := {L : Language Bool | ∃ (P V), IsInteractiveProof P V L}`.

**Claim-117.c (NP ⊆ IP).** For `L ∈ Complexity.NP` (certificate length `C(|x|+1)^c`,
verifier `V ∈ P` on `x ++ u`): the one-round protocol "P sends `u`; `V` accepts iff
`|u| = C(|x|+1)^c ∧ x ++ u ∈ V`" is an interactive proof with soundness error `0`.
Completeness: the witness `u`; soundness: for `x ∉ L` no `u` is accepted. Machine content:
package the `P`-decider (`mem_P_iff`) as a PPT strategy (time poly in `|x|` since `|u|` is
poly in `|x|`). Optional (the text states it as trivial).

**Claim-117.d (IP = PSPACE).** Cited (Shamir). Deferred; nothing downstream.

**Def-117.e (graphs, `σ(G)`, isomorphism).** Graphs on `n` vertices are
`SimpleGraph (Fin n)`; for `σ : Equiv.Perm (Fin n)`, `σ(G) := G.map σ.toEmbedding`
(edges `{σ u, σ v}`); `G1 ≅ G2 :⇔ ∃ σ, σ(G1) = G2`. Lemmas: `σ(τ(G)) = (σ * τ)(G)`
(`SimpleGraph.map_map`, note `Equiv.Perm` multiplication order), `1(G) = G`
(`map_id`), `σ(G) = H ↔ G = σ⁻¹(H)` (`map_symm`/`comap_symm`), injectivity of
`G ↦ σ(G)`, `≅` is an equivalence relation, and the bridge
`Nonempty (G1 ≃g G2) ↔ G1 ≅ G2` (`SimpleGraph.Iso.map σ G1 : G1 ≃g σ(G1)` one way;
`RelIso.toEquiv` and `map_adj` the other). Finiteness: `Fintype (SimpleGraph (Fin n))`
(Mathlib `Basic.lean:110`) and `Fintype (Perm (Fin n))`. Decidability of `G = H` and of
`G.Adj`: use classical decidability at the concrete layer; the machine layer works on the
adjacency-matrix encoding (Inf-4.1).

**Def-118.a (`L_iso`, `L_niso`, `R_iso`).** Typed: `L_iso n := {(G0, G1) | G0 ≅ G1}`,
`R_iso (G0,G1) σ :⇔ σ(G0) = G1`, `L_niso n := {(G0, G1) | ¬ G0 ≅ G1}` (same vertex count by
typing). String forms via Inf-4.1 (pairs of adjacency matrices; malformed strings decode to
a default pair and are *not* in `L_niso`). The text's "same number of vertices" condition is
the typing.

**Claim-118.b (`L_iso ∈ NP`).** String level: certificate = encoding of `σ` (length
`≤ C(|x|+1)^c`), verifier computes `σ(G0)` and compares with `G1` in polynomial time.
Optional; the typed `R_iso` is what Defs 119.5/121.x consume.

**Claim-118.c (`L_niso ∈ coNP`).** The complement (malformed, or isomorphic) is in NP by
Claim-118.b. Deferred.

**Prot-118.3 (GNI).** Common input `x = (G0, G1)`, `n` vertices each. One iteration:
`V` draws `b : Bool` and `σ ∈ S_n` uniformly, sends `H := σ(G_b)`; `P` replies `b'`; `V`
accepts iff `b' = b`. Honest (unbounded) prover: `b' := decide (H ≅ G0) ? 0 : 1`
(classical). `n`-fold: `n` sequential iterations with fresh `(b_i, σ_i)`; `V` accepts iff all
accept; modelled as a `2n`-round protocol with verifier coins `Fin n → Bool × Perm (Fin n)`.
The prover's reply is decoded as a bit (any message other than `[true]` counts as `0`).
*Text issue:* "Repeat the procedure `|G1|` times" means `n` times.

**Lem-119.a.** If `σ₀(G0) = G1` then for uniform `σ ∈ S_n` the samplers `σ ↦ σ(G0)` and
`σ ↦ σ(G1)` have the same distribution: `σ(G1) = (σ * σ₀)(G0)` and `σ ↦ σ * σ₀` is a
bijection (`Equiv.mulRight`, `uprob_comp_equiv`). Hence for uniform `(b, σ)`, the pair
`(b, σ(G_b))` has the distribution of `(b, σ(G0))` with `b` independent of the graph.

**Lem-119.c (adaptive guessing).** For every finite `W` and every family
`g : (i : Fin n) → (Fin i → Bool) → W → Bool`:
`uprob (fun (b, w) : (Fin n → Bool) × W => ∀ i, b i = g i (fun j => b (Fin.castLT j _)) w) = 2^{-n}`.
Proof: for each `w` exactly one `b` satisfies the constraint (recursion on `n`, `Fin.snoc`),
then `uprob_eq_one_div_card`/`uprob_prod`. This is the engine of all `2^{-n}` soundness
bounds against adaptive provers.

**Lem-119.b (GNI soundness).** If `G0 ≅ G1` (via `σ₀`) then for every `P*` (coins `r`) and
`z`: `Pr_{b, σ, r}[∀ i < n, b'_i = b_i] ≤ 2^{-n}` where `b'_i` is `P*`'s reply after seeing
`H_1, …, H_i`. Proof: change variables `σ'_i := if b_i then σ_i * σ₀ else σ_i` (bijection of
`(b, σ)`), so every `H_i = σ'_i(G0)` is a function of `σ'` alone; then `b'_i = g_i(σ', r)`
and Lem-119.c (with `W := (Fin n → Perm) × ρ_{P*}`) gives exactly `2^{-n}`.

**Lem-119.d (GNI completeness).** If `¬ G0 ≅ G1` then for all `b, σ`: `σ(G_b) ≅ G_b` and
`¬ σ(G_b) ≅ G_{1−b}` (Lem-120.b), so the honest prover's `b' = b`; the `n`-fold verifier
accepts with probability `1` (`uprob_eq_one_of_forall`).

**Prop-118.4.** Protocol 118.3 (`n`-fold) is an interactive proof for `L_niso`: completeness
Lem-119.d (witness `y` irrelevant), soundness `2^{-n(x)} ≤ ε(|x|)` negligible (Inf-4.4),
`V` PPT (Inf-4.2; `σ(G)` and the comparison `b' = b`). *Text issues:* the proof writes
`G1, G2` for `G0, G1`; "the Prover runs in exponential time" is modelled by an arbitrary
function; "each iteration is independent of all prior iterations" hides the adaptive-prover
argument (Lem-119.b).

**Def-119.5 (efficient prover).** `(P, V)` is an interactive proof for `L` with efficient
prover w.r.t. `R_L` if `P` is PPT (time poly in `|x|`, witness `y` as auxiliary input) and
completeness holds for **every** `y ∈ R_L(x)` (Def-116.1 asks for *some* `y`).

**Def-119.e (interactive argument).** Soundness quantified over nuPPT `P*` only (D4
machines with advice; `P*` may receive `z`). Optional.

**Claim-119.f.** "A polynomial-time prover would imply `L_niso ∈ NP`": informal, not a
precise theorem (a deterministic PPT prover together with the public-coin verifier gives an
NP witness only after de-randomization). Deferred, not formalized.

**Prot-120.6 (GI).** Common input `(G0, G1)`, prover witness `σ` with `σ(G0) = G1`. One
iteration: `P` draws `π ∈ S_n` uniformly, sends `H := π(G0)`; `V` sends uniform `b`; `P`
sends `γ := if b then π * σ⁻¹ else π` (as functions: `γ = π ∘ σ⁻¹` so that
`γ(G1) = π(σ⁻¹(G1)) = π(G0) = H`); `V` accepts iff `γ(G_b) = H`. `n`-fold: sequential with
fresh `π_i`, `b_i`. `V`'s message is decoded as a bit by `P`. *Text issue:* the composition
order of `π · σ^{-1}` must be fixed (right-to-left as functions).

**Lem-120.a.** `σ(G0) = G1 → π(G0) = H → (π * σ⁻¹)(G1) = H` (`map_map`, `map_symm`);
hence the honest prover is accepted with probability `1` in every iteration, for every
witness `σ` (Def-119.5's "every `y`").

**Lem-120.b.** `¬ G0 ≅ G1 → ¬ (H ≅ G0 ∧ H ≅ G1)` (symmetry and transitivity of `≅`).

**Lem-120.c (single-iteration soundness).** If `¬ G0 ≅ G1` then for every `P*` (coins `r`)
and `z`: `Pr_{b, r}[γ(G_b) = H] ≤ 1/2` where `H = H(r)` and `γ = γ(r, b)`: for fixed `r`,
by Lem-120.b at most one `b` admits a `γ` with `γ(G_b) = H`; `b` is uniform and independent
of `H` (`uprob_prod`, `uprob_bool_prod`).

**Lem-120.d (`n`-fold soundness).** `Pr[all n iterations accept] ≤ 2^{-n}` for every
`P*`: with `g_i(b_{<i}, r) :=` the unique good bit for `H_i` (or `false`), acceptance in
all rounds implies `∀ i, b_i = g_i(b_{<i}, r)`; apply `uprob_mono` and Lem-119.c. This also
formalizes the remark "the protocol can be repeated … to drive the error as low as desired".

**Prop-120.7.** Protocol 120.6 (`n`-fold) is an interactive proof for `L_iso` with efficient
prover w.r.t. `R_iso`: completeness Lem-120.a for every witness, soundness `2^{-n} ≤ ε(|x|)`
(Inf-4.4), `P` and `V` PPT (permutation composition/inversion, `σ(G)`, graph equality:
Inf-4.2). *Text errors:* stated "for `L_niso`" (it is `L_iso`); the proof's
"`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" has the maps reversed and uses `G1, G2` for
`G0, G1`; the proof only argues `1/2` per iteration.

### §4.6 Zero-knowledge — `ZeroKnowledge/Defs.lean`, `GraphIsomorphismZK.lean`

**Def-121.1 (HVZK).** `(P, V)` an interactive proof with efficient prover for `L` with
witness relation `R_L`. HVZK if ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV x y z) (S x z) D ≤ ε(|x|)` where
`viewV x y z : ρ_P × ρ_V → View_V` is the honest verifier's view sampler and
`S x z : ρ_S → View_V` (`S` outputs a *view*, i.e. `(x, z, r_V, messages received)`).
*Text issue:* `e(n)` with `n` undefined — read `n = |x|`.

**Def-121.2 (ZK).** ∀ PPT `V*` ∃ PPT `S` ∀ nuPPT `D` ∃ negligible `ε` ∀ `x ∈ L`,
`y ∈ R_L(x)`, `z`: `distAdv (viewV* x y z) (S x z) D ≤ ε(|x|)`. Deviation (D8): `S` strict
PPT instead of expected PPT (stronger demand on `S`). `V*` is PPT with auxiliary input `z`
(the text's remark on non-uniformity, Claim-122.c).

**Def-121.a (expected PPT).** Expected running time over the machine's own coins polynomial.
Deferred (D8); would need a sampler with unbounded coin usage.

**Def-122.a (perfect / statistical ZK).** Perfect: the two distributions identical for all
`x, y, z` (then `distAdv = 0` for every `D`). Statistical (campaign addition, needed for
Thm-122.3): `statDist (view distribution) (S distribution) ≤ δ(|x|)` with `δ` negligible —
implies Def-121.2 for every `D` by `distAdv_le_statDist`, and `δ := 2^{-n}` is the GI case.
*Note:* the GMR definition lets a perfect simulator output `⊥` with probability `≤ 1/2`;
the text does not.

**Claim-122.b (view vs output).** Replacing `view_{V*}` by `out_{V*}` gives an equivalent
definition: (⇒) `out` is a PPT function of the view, so `S' := out_{V*} ∘ S` works by
closure (`distAdv_sunglassRed`, Lem-71.5); (⇐) apply the output-based definition to the
PPT `V*'` that outputs its own view. Optional.

**Claim-122.c.** ZK against PPT `V*` with auxiliary input already covers nuPPT `V*` (advice
as part of `z`, simulator receives the same advice). Deferred (needs a nuPPT verifier
notion; remark only).

**Thm-122.3.** Protocol 120.6 is a zero-knowledge interactive proof for `L_iso` with the
canonical witness relation `R_iso`. Formalized as: (a) Prop-120.7; (b) **single iteration**:
for every `V*` (any strategy with finite coins at the concrete layer; PPT at the asymptotic
layer) the truncated simulator `S_n` (Alg-123.4) satisfies
`statDist (viewV* x σ z) (S_n x z) ≤ 2^{-n}` for all `(G0,G1) ∈ L_iso`, `σ ∈ R_iso`, `z`
(Thm-122.3.trunc), hence statistical ZK with `ε = 2^{-n(x)}` (Inf-4.4) and `S_n` PPT
(Claim-123.d); (c) the `n`-fold protocol: ZK under the sequential-composition hypothesis
Claim-123.c (deferred). *Text issue:* "perfect" becomes statistical because of truncation
(D8); the text proves one iteration only.

**Thm-122.3.hv (HVZK, perfect, by reindexing).** Simulator: draw `b : Bool`, `γ ∈ S_n`
uniformly, output `(x, z, b, [γ(G_b), γ])`. For `σ(G0) = G1`, the honest view sampler
`(π, b) ↦ (x, z, b, [π(G0), if b then π * σ⁻¹ else π])` equals the simulator sampler
composed with the bijection `(π, b) ↦ (if b then π * σ⁻¹ else π, b)` (Lem-120.a), so the
two distributions are identical (`acceptProb_comp_equiv`). Same shape as
`Schnorr.schnorr_hvzk` (`reindex`), which is the template.

**Alg-123.4 (GI simulator, truncated).** `S_n(x, z)` with coins
`(b', π, r) : Fin n → Bool × Perm (Fin n) × ρ_{V*}`: for attempt `k = 0, …, n−1`: `H_k := π_k(G_{b'_k})`;
`b_k :=` bit decoded from `V*.next x z r_k [H_k]`; if `b_k = b'_k` output
`some (x, z, r_k, [H_k, π_k])` (the view of `V*`), else continue; after `n` failures output
`none` (`⊥`). Deviation: truncation (strict PPT) instead of restart until success.

**Lem-123.5.** For `(G0,G1) ∈ L_iso`, in one attempt: (i) the sampler
`(b', π) ↦ (b', π(G_{b'}))` has the distribution of `(b', π) ↦ (b', π(G0))`, so `H` is
independent of `b'` and distributed as `π(G0)` (Lem-119.a); (ii) for every function
`V*` and every `z`: `Pr_{b', π, r}[V*(x, z, r, [H]) = b'] = 1/2` (`b` depends on
`(H, r, z)` only; condition on `(H, r)` and use `uprob_bool_prod`).

**Claim-123.a.** Expected number of attempts of the untruncated simulator is `2`. Deferred
(Def-121.a).

**Claim-123.b (perfect simulation given success).** For every view `v`:
`Pr_{b', π, r}[attempt outputs v ∧ b = b'] = (1/2) · Pr_{π, r}[viewV*(x, σ, z)(π, r) = v]`.
Proof: for fixed `r` the real execution is `π ↦ (H = π(G0), b = V*(H, r), γ = if b then π * σ⁻¹ else π)`;
the successful attempts are `(b', π')` with `H = π'(G_{b'})`, `b = V*(H, r) = b'`, output
`π'`; the map `(b', π') ↦ π := if b' then π' * σ else π'` (so that `π(G0) = H` and
`γ = π'`) is a bijection from `{(b', π') | success}` onto `Perm` with `b' = b(π)`; hence the
two counts agree up to the factor `1/2` from the `b'` coordinate (`uprob_eq_of_equiv`,
`uprob_prod`). Model: `TCSlib.MPC.BGW.linear_perfectPrivacy` (perfect privacy by a coin
bijection).

**Thm-122.3.trunc.** `Pr[S_n = ⊥] = 2^{-n}` (attempts use disjoint coins; each fails with
probability exactly `1/2` by Lem-123.5(ii); `uprob_prod`/`OneWay.uprob_pi_forall`) and for
every `v`: `Pr[S_n = some v] = (1 − 2^{-n}) · Pr[view = v]` (sum over the first successful
attempt of `2^{-k} · (1/2) · Pr[view = v]`, Claim-123.b); therefore
`statDist (S_n) (some ∘ view) = 2^{-n}` and `distAdv (S_n x z) (some ∘ viewV* x σ z) D ≤ 2^{-n}`
for every `D` (`distAdv_le_statDist`).

**Claim-123.c.** Sequential repetition of a ZK protocol is ZK (§7.2.1). Deferred (outside
Chapters 2–4; needs the auxiliary-input hybrid over iterations). Stated as a hypothesis
where the `n`-fold theorems need it.

**Claim-123.d.** `S_n` is strict PPT when `V*` is: `n` attempts of (sample, `π(G)`, one call
of `V*` with fresh coins, compare) — plan `Randomized/Repetition.lean` on top of
`Turing.FinTM.exists_loopFindTM` (first accepting round's payload). Machine-level; the
load-bearing infrastructure item of the chapter together with Claim-128.a.

### §4.7 Zero-knowledge for NP — `ZeroKnowledge/NP.lean`

**Thm-124.1.** If one-way permutations exist then every language in NP has a ZK proof.
Formalized in three forms: **(A, core)** for every `(L, R_L)` and every Levin reduction
`(f, w)` from `(L, R_L)` to `(3COL, R_3COL)` (Def-124.a, string level through Inf-4.1), the
composed protocol — both parties compute `x' := f(x)`, the prover additionally `y' := w(x, y)`,
then run Protocol 127.5 — is a ZK proof with efficient prover for `L` (Claim-124.d applied to
Prop-127.6, with the commitment scheme from Thm-126.4). **(B, optional/deferred)** "every
`L ∈ Complexity.NP`" follows from (A) given string-level Levin NP-hardness of 3COL
(Claim-124.b + Claim-124.c), stated as an explicit hypothesis. **(C, optional)** with an
*unbounded* honest prover a Karp reduction suffices (the prover finds a colouring of `f(x)`
classically) — but Def-121.2 requires an efficient prover, so (C) is only a remark.
*Text issues:* "Cook's reduction can be applied to the witness `y`" requires a Levin
reduction, never defined in the text; "execute protocol `(P, V)` on `x'`" should be
`(P', V')`; the theorem silently needs a hard-core predicate for the OWP (Thm-87.3).

**Def-124.a (Levin reduction).** `(f, w)` with `PolyTimeComputable f`, `w` polynomial-time
in `(x, y)` (two-argument via `pairEncode`), `∀ x, x ∈ L ↔ f x ∈ L'`, and
`∀ x y, R_L x y → R_{L'} (f x) (w x y)`. Extends `Complexity.PolyTimeReducible` (Karp).

**Claim-124.b (3COL NP-complete, string level).** `3COL := {x | (decodeGraph x).Colorable 3}`;
NP membership (colouring certificate) and NP-hardness via `SAT3 ≤ₚ 3COL`. The repository
has `Complexity.SAT3_NPComplete` and the graph-level `SATtoColor.SATtoColorReduction`
(on `SATtoColor.Sat3 V`, a different 3SAT syntax from `CNF.decode`); the poly-time string
reduction machine is missing — large machine-building task. Deferred.

**Claim-124.c (witness transformation 3SAT → 3COL).** The colouring built from a satisfying
assignment is `SATtoColor.sat3Coloring` (declared `private`; its validity is the content of
`SATtoColorCompleteness`). A Levin reduction needs it as a poly-time string function.
Deferred with Claim-124.b.

**Claim-124.d (ZK transfers along Levin reductions).** If `(P', V')` is a ZK proof with
efficient prover for `(L', R_{L'})` and `(f, w)` is a Levin reduction from `(L, R_L)`, then
`P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)` is a ZK proof with efficient prover for
`(L, R_L)`: completeness from `R_L x y → R_{L'} (f x) (w x y)`; soundness: `x ∉ L → f x ∉ L'`
and a cheating `P*` for `x` is a cheating prover for `f x`; ZK: for `V*`, let
`V*'(x', (x, z)) := V*(x, z)` (recovers `x` from its auxiliary input, ignores `x'`), then
`viewV*[P(x,y) ↔ V*(x,z)] = viewV*'[P'(f x, w x y) ↔ V*'(f x, (x,z))]` up to relabelling,
and `S(x, z) := S'(f x, (x, z))`; PPT-ness of `P`, `V`, `V*'`, `S` by composition with `f`,
`w`. Negligibility: `ε'(|f x|)` with `|f x| ≤ poly(|x|)` and `|f x| ≥ …` — needs
`f` length-nondecreasing or a `Negligible.mono`-type lemma for polynomially related
parameters (record).

**Claim-124.e.** General one-way functions suffice (Naor commitments). Deferred.

**Def-124.f (3COL, `R_3COL`).** Typed: `3COL n := {G : SimpleGraph (Fin n) | G.Colorable 3}`
(`= Nonempty (G.Coloring (Fin 3))`, literally `SATtoColor.Is3Colorable G`); witness
relation `R_3COL G c :⇔ ∀ u v, G.Adj u v → c u ≠ c v` for `c : Fin n → Fin 3`
(`SimpleGraph.Coloring.mk`). Colours `{1,2,3}` are `Fin 3`.

**Claim-125.a.** For `m ≥ 1`: `(1 − 1/m)^{n·m} ≤ exp(−n) ≤ 2^{-n}`. From
`Real.one_sub_div_pow_le_exp_neg` (`(1 − t/N)^N ≤ exp(−t)` with `N = n·m`, `t = n`) or
`Real.add_one_le_exp`. Pure real analysis; the text writes `≈ e^{-n}`.

### §4.7.1 Commitments — `ZeroKnowledge/Commitment.lean`

**Def-126.3 (commitment scheme).** A deterministic polynomial-time `Com` and polynomial `ℓ`
with (1) binding: ∀ `n`, ∀ `v0 ≠ v1 ∈ {0,1}^n`, ∀ `r0, r1 ∈ {0,1}^{ℓ(n)}`:
`Com(v0, r0) ≠ Com(v1, r1)`; (2) hiding: ∀ nuPPT `D` ∃ negligible `ε` ∀ `n`,
`v0, v1 ∈ {0,1}^n`: `distAdv (fun r => Com n v0 r) (fun r => Com n v1 r) D ≤ ε(n)`.
Concrete: `Com n : (Fin n → Bool) → (Fin (ℓ n) → Bool) → C n`. Deviation (DQ4): `n` is an
explicit argument (the text infers it from `|v|`). *Text error:* binding as printed omits
`v0 ≠ v1` and is unsatisfiable (`v0 = v1`, `r0 = r1`).

**Claim-126.a (multi-value hiding).** For every commitment scheme, polynomial `q`, nuPPT `D`
∃ negligible `ε` ∀ `n`, `(v_i), (v'_i) ∈ ({0,1}^n)^{q(n)}`:
`distAdv ((r_i) ↦ (Com n v_i r_i)_i) ((r_i) ↦ (Com n v'_i r_i)_i) D ≤ ε(n)`. Proof: hybrids
`H_k` (coordinates `< k` from `v'`, `≥ k` from `v`), `exists_hybrid_gap`; the reduction for
index `k` gets a commitment to `v_k` or `v'_k`, samples the other coordinates' commitments
itself (`Com` is poly-time; `acceptProb_update` plants the challenge), so advantage
`≥ ε_D/q(n)`; non-uniform choice of `k` or the averaged `mixDist` reduction. Generalizes
`exists_multicopyRed_ge` (identical pair in all coordinates) — a per-coordinate version is
needed (new concrete lemma; propose it for `Indistinguishability`-style reuse but keep a
private copy here per the ownership rule). Needed by Claim-129.d.

**Thm-126.4.** If `f` is a one-way permutation (length-preserving bijection at every `n`,
Def-27.3) with hard-core predicate `h` (Def-78.3), then Alg-127.a is a commitment scheme:
`Com` poly-time (from `f`, `h` poly-time), binding (Claim-127.b), hiding (Claim-127.c for one
bit, Claim-127.d for `n` bits). Unconditional-from-OWP form: apply Goldreich–Levin
(Thm-87.3) to get `(g, ⟨·,·⟩)` with `g(x, r) = (f x, r)` a OWP — optional, depends on the
Chapter 3 asymptotic GL theorem. *Text issue:* OWP here is a single function (Thm 79.4's
usage), not the collection of Def 55.1; the existence of `h` is not mentioned.

**Alg-127.a (construction).** `Com₁ n b r := (f n r, b ⊕ h n r)` for `r ∈ {0,1}^n`
(`ℓ(n) = n`); `Com n v (r_1, …, r_n) := (Com₁ n (v i) (r i))_i` (`ℓ(n) = n²`). With the
Garg layer: `owpGen f B : α × Unit → α × Unit × Bool` is `Com₁(0, ·)` and `owpGenNot f B`
is `Com₁(1, ·)` up to the `Unit` coordinate.

**Claim-127.b (binding).** `f n` injective ⇒ `Com₁ n b0 r0 = Com₁ n b1 r1 → r0 = r1 → b0 = b1`;
for the `n`-bit scheme, `v0 ≠ v1` differ at some `i`, and coordinate `i` separates.

**Claim-127.c (single-bit hiding, concrete).** For every `D : C → ρ → Bool`:
`predProb (owpPair f) B (owpPredictor D flip) = 1/2 ± distAdv (Com₁ 0) (Com₁ 1) D / 2`
for the appropriate `flip`, i.e. a distinguisher with advantage `ε` yields a predictor of
`h(r)` from `f(r)` with success exactly `1/2 + ε/2` — this **is**
`predProb_owpPredictor_false`/`_true` with `β := Unit` (`acceptProb` is invariant under the
`Unit` coordinate, `acceptProb_fst`). Asymptotic: if `h` is hard-core then
`distAdv ≤ 2 ε_h(n)` with the predictor nuPPT (one extra coin, one call of `D`). "Identical
to the proof of Theorem 104.4" (prediction lemma Lem-73.8 + XOR trick).

**Claim-127.d (bitwise hybrid, "show this!").** Hiding of `Com₁` ⇒ hiding of `Com`:
hybrids over the `n` bits (`exists_hybrid_gap`), the reduction plants the challenge
commitment at bit `k` and samples the others (`acceptProb_update`); advantage `≥ ε/n`;
`Negligible.mul_pow`. Special case of Claim-126.a with `q = n`, values single bits.

### §4.7.2 Graph 3-colouring — `ZeroKnowledge/ThreeColoring.lean`

**Prot-127.5.** Common input `G : SimpleGraph (Fin n)` with `m := |E|` (`E := G.edgeFinset`);
prover witness `c : Fin n → Fin 3` with `R_3COL G c`. One iteration: `P` draws
`π ∈ Perm (Fin 3)` and `r_i ∈ {0,1}^{ℓ(n)}` (`i < n`) uniformly and sends
`com_i := Com n (pad (π (c i))) (r_i)`; `V` sends a uniform edge `e = {i, j} ∈ E`; `P` sends
the openings `(π (c i), r_i, π (c j), r_j)`; `V` accepts iff `e ∈ E`,
`Com n (pad c'_i) r_i = com_i`, `Com n (pad c'_j) r_j = com_j` and `c'_i ≠ c'_j`.
`n·m`-fold: sequential with fresh `π`, `r`. Deviations: the opening check (the text's
"`V` accepts iff `c'_i ≠ c'_j`" is unsound without it); colours padded to `n` bits
(DQ4, requires `n ≥ 2`); if `E = ∅` the verifier accepts outright (every edgeless graph is
3-colourable; the text's "random edge" is undefined). *Text errors:* witness listed as
`c0, …, cm` (should be `c1, …, cn`).

**Claim-127.e (completeness).** For `R_3COL G c`, any `π`, `r`: `π (c i) ≠ π (c j)` on every
edge (`Coloring.valid`, `π` injective) and the openings verify; `V` accepts with
probability `1` in every iteration (`uprob_eq_one_of_forall`).

**Lem-127.f (committed colouring).** From binding: for each commitment string `com`, there
is at most one `v ∈ {0,1}^n` with `∃ r, Com n v r = com`; let `c̃ k : Option (Fin 3)` be the
colour it decodes to (if any). An opening accepted by `V` on edge `{i, j}` forces
`c'_i = c̃ i`, `c'_j = c̃ j`. If `¬ G.Colorable 3` then for every `c̃` there is an edge
`{i, j} ∈ E` with `c̃ i = c̃ j` or one endpoint undefined (else `c̃` would be a proper
colouring, after sending `none` to any colour), on which no opening is accepted.

**Lem-127.g (adaptive sequential soundness, escape `1/m`).** For `k` rounds with uniform
challenges `e_i ∈ Fin m` (or `E`) and any `Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m)`
with `∀ i h w, (Bad i h w).Nonempty`:
`uprob (fun (e, w) => ∀ i, e i ∉ Bad i (e|_{<i}) w) ≤ (1 − 1/m)^k`. Proof by induction with
`uprob_prod`. Lem-119.c is the equality case `m = 2`, `|Bad| = 1`.

**Claim-127.h (soundness of 127.5).** If `¬ G.Colorable 3` (and `m ≥ 1`) then for every
`P*` (coins `r`) and `z`: `Pr[V accepts all n·m iterations] ≤ (1 − 1/m)^{n·m} ≤ e^{-n}`:
in iteration `i`, given the history, the committed colouring `c̃_i` has a bad edge
(Lem-127.f), the verifier's uniform edge hits it with probability `≥ 1/m` and then the
iteration rejects; Lem-127.g, Claim-125.a. *Text error:* "repeated `|E|²` times".

**Prop-127.6.** Protocol 127.5 is a ZK proof for 3COL: (a) interactive proof with efficient
prover w.r.t. `R_3COL`: Claim-127.e, Claim-127.h with `e^{-n(x)}` negligible in `|x|`
(Inf-4.4), `P`, `V` PPT (`Com` poly-time, edge sampling per DQ1, Inf-4.2); (b) ZK of the
single iteration: Prop-128.8 + Claim-128.a; (c) the `n·m`-fold protocol's ZK under
Claim-123.c (deferred).

**Alg-128.7 (3COL simulator, truncated).** `S(x, z)` with coins per attempt
`(e' = {i', j'} ∈ E, (a, b) ∈ {(u, v) : Fin 3 × Fin 3 | u ≠ v}, r : Fin n → {0,1}^{ℓ(n)}, r_{V*})`:
`c'_{i'} := a`, `c'_{j'} := b`, `c'_k := 0` otherwise; `com_k := Com n (pad c'_k) r_k`;
`e :=` edge decoded from `V*.next x z r_{V*} [com]`; if `e = e'` output
`some (x, z, r_{V*}, [com, (a, r_{i'}, b, r_{j'})])` else next attempt; after `n·m` attempts
output `none`. *Text issues:* "`k ∈ [m] \ {i', j'}`" should be `[n]`; `(i, j) = (i', j')`
is equality of unordered edges.

**Claim-128.a.** `S` is strict PPT when `V*` is (loop of `n·m` attempts, each with `n`
evaluations of `Com` and one call of `V*`): Inf-4.3.

**Prop-128.8.** ∀ PPT `V*` ∀ nuPPT `D` ∃ negligible `ε` ∀ `G ∈ 3COL`, `c ∈ R_3COL(G)`, `z`:
`distAdv (viewV* G c z) (S G z) D ≤ ε(|x|)`. Proof chain (all at the concrete layer, then
negligibility): `S ≡ S'` (Claim-129.a), `distAdv(S', S'') ≤ (n·m) · ε_Com` (Claim-129.d),
`statDist(S'', view) ≤ e^{-n}` (Claim-129.c); triangle inequality, `Negligible.add`,
`Negligible.mul_pow`. The hardest theorem of the chapter. *Text issues:* hybrid count
`2n|E|` (there are `n|E|` attempts); the sub-hybrid `S̃_e` over `6|E|` values of
`(i', j', π)` is unnecessary (the reduction samples them; non-uniformly one may fix the
best); typo "in `S̃_{e+1}` … whereas in `S̃_{e+1}`"; the last step uses multi-value hiding
(Claim-126.a) and closure (Lem-71.5).

**Claim-129.a (`S ≡ S'`).** `S'` receives the witness `c` and sets
`(c'_{i'}, c'_{j'}) := (π (c i'), π (c j'))` for uniform `π ∈ S_3` instead of a uniform
distinct pair; since `c i' ≠ c j'` on an edge, Lem-129.b makes the two samplers equal in
distribution; everything else is identical.

**Lem-129.b.** For `a ≠ b : Fin 3`, `π ↦ (π a, π b)` is a bijection
`Perm (Fin 3) ≃ {p : Fin 3 × Fin 3 // p.1 ≠ p.2}` (both sides have `6` elements,
`Fintype.card_perm`; injectivity since a permutation of `Fin 3` is determined by two values;
or `decide` after enumeration).

**Claim-129.c (`S''`).** `S''` commits to `pad (π (c k))` for **all** `k` (like the honest
prover) but still restarts unless `e = e'`: (i) `e'` is independent of `V*`'s reply (the
commitments do not depend on `e'`), so each attempt succeeds with probability exactly `1/m`
and `Pr[S'' = ⊥] = (1 − 1/m)^{n·m} ≤ e^{-n}` (`uprob_prod`, Claim-125.a); (ii) conditioned
on success the output is the honest view (commitments and openings with the prover's
distribution of `(π, r)`, edge `e` chosen by `V*`), as in Claim-123.b; hence
`statDist (S'') (some ∘ view) ≤ e^{-n}` and `distAdv ≤ e^{-n}` for every `D`.

**Claim-129.d (`S' ≈ S''`).** `S'` and `S''` differ only in the `n − 2` unopened commitments
of each attempt (`pad 0` versus `pad (π (c k))`). Hybrids `S_k` (attempts `< k` as `S''`,
`≥ k` as `S'`), `k = 0, …, n·m`; `exists_hybrid_gap` gives an adjacent pair with gap
`≥ δ/(n·m)`; the reduction for index `k` samples `(e', π, r_{V*})` of attempt `k` and all
other attempts itself, receives the commitment vector for the unopened positions from the
multi-value hiding challenger (Claim-126.a with `q = n`, values `pad 0` vs `pad (π (c ·))`,
the two opened positions committed by the reduction), simulates the restart logic, and runs
`D`; by `distAdv_sunglassRed`/`acceptProb_bind` its advantage equals the hybrid gap. It is
nuPPT by closure (Lem-71.5). Conclusion: `distAdv(S', S'') ≤ n·m · ε_Com(n)`, negligible.

### Appendix B

**Def-191.10 (DP).** Deterministic polynomial time = `Complexity.P` (exists). Alias only.

**Def-191.11 (NP via witness relations).** `L ∈ NP` iff ∃ `R_L ⊆ {0,1}* × {0,1}*`
poly-time recognizable and polynomial `p` with `x ∈ L ↔ ∃ y, |y| ≤ p(|x|) ∧ (x, y) ∈ R_L`;
`R_L(x) := {y | (x, y) ∈ R_L}`. Existing: `Complexity.mem_NP_iff_exists_length_le` is this
form with `p(N) = C(N+1)^c` and the pair `pairEncode x y` in a `P` language — the bridge is
a one-line unfolding. Chapter 4 consumes only the typed relation `R : X → Y → Prop` with
`L = {x | ∃ y, R x y}`. *Text error:* "`R_L(x) = {y : (x, y) ∈ L}`" should read `∈ R_L`.

**Def-192.12 (BPP).** Not used by Chapter 4; optional, trivial once `Randomized/PPT.lean`
is frozen.

### Infrastructure specific to Chapter 4

**Inf-4.1 (encodings).** `encGraph : SimpleGraph (Fin n) → List Bool` (adjacency matrix
`Fin n → Fin n → Bool`, row-major, prefixed by `n` in unary or binary via `pairEncode`),
`decGraph : List Bool → Σ n, SimpleGraph (Fin n)` total with default; same for
`Perm (Fin n)` (image list), `Fin 3`-colourings, message lists (`pairEncode`-folded) and
views. Length bounds `|encGraph G| ≤ C·(n+1)²`, decode-encode identities, and
`PolyTimeComputable` of the (de)coders. New file `ZeroKnowledge/Encoding.lean` (proposed
split; not in the plan's layout).

**Inf-4.2 (honest parties as machines; DQ1).** `PolyTimeComputable` facts for `σ(G)`,
`π * σ⁻¹`, `G = H`, `e ∈ E`, `Com` evaluation on encoded inputs, and the sampling of
`σ ∈ S_n`, `e ∈ E`, `π ∈ S_3` from coins (option A: near-uniform with error `2^{-n}`,
machine level, difficulty 5; option B: typed coin spaces, difficulty 3). Every `IsPPT`
side-condition of Props 118.4, 120.7, 127.6 lives here.

**Inf-4.3 (bounded restart loops).** The plan's `Randomized/Repetition.lean`: a PPT that
runs a PPT body up to `N(|x|)` times with fresh coins and returns the first accepted payload
(`exists_loopFindTM`). Consumed by Claim-123.d and Claim-128.a.

**Inf-4.4 (negligibility in `|x|`).** If `|encGraph G| ≥ n(G)²/C` (or `n ≥ Nat.sqrt (|x| / C)`)
then `fun N => (2:ℝ)⁻¹ ^ Nat.sqrt (N / C)` and `fun N => Real.exp (−Nat.sqrt (N / C))` are
negligible (`negligible_two_pow_neg` composed with the sub-polynomial growth of `sqrt`;
`Negligible.mono`). Converts the chapter's per-vertex bounds into Def-116.1's `ε(|x|)`.

## 4. Text errors and gaps found in Chapter 4 (for the plan's error list)

1. Proposition 120.7 says "interactive proof for `L_niso`"; it is for `L_iso` (already in the plan).
2. Definition 126.3, binding: the quantifier omits `v0 ≠ v1`; as printed the condition is unsatisfiable.
3. Proposition 127.6's proof: "repeated `|E|²` times" vs. the protocol's `n|E|` (already in the plan).
4. Protocol 127.5 lists the witness as `c0, c1, …, cm`; it is `c1, …, cn`. Simulator 128.7 writes "`k ∈ [m] \ {i', j'}`" for `[n]`.
5. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`": without checking that the openings match the commitments the protocol is unsound; also undefined for `E = ∅`; and `Com` applied to 2-bit colours has security parameter 2 under Definition 126.3 (the colour must be padded or `Com` given `1^n`).
6. Proof of Proposition 120.7: "`π(H) = G1` and `σ(π(H)) = σ(G1) = G2`" reverses the maps and renames the graphs; the correct identities are `π(G0) = H`, `(π∘σ⁻¹)(G1) = H`.
7. Theorem 122.3 claims (perfect) ZK for Protocol 120.6 with `n` iterations; the proof covers one iteration and relies on §7.2.1 (sequential composition), which is outside Chapters 2–4.
8. Definitions 121.1, 121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined (intended `n = |x|`).
9. Proof of Proposition 128.8: the hybrid count `2n|E|` does not match the `n|E|` attempts; "in `S̃_{e+1}` … whereas in `S̃_{e+1}`" (second should be `S̃_e`); the `6|E|`-step sub-hybrid is unnecessary.
10. §4.7, Step 2: "Cook's reduction can be applied to the witness" needs a Levin (witness-preserving) reduction, never defined; "execute protocol `(P, V)` on `x'`" should be `(P', V')`.
11. Theorem 126.4 uses a single one-way permutation `f` with a hard-core predicate `h`, whereas Definition 55.1 defines OWPs as collections and the existence of `h` (Theorem 87.3) is not invoked.
12. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
13. Proof of Proposition 118.4 uses `G1, G2` for `G0, G1`; "exponential time prover" is only an upper bound on what an unbounded prover needs.
14. The chapter never states that "choose a random permutation `σ ∈ S_n`" / "a random edge" cannot be done exactly by a PPT with a bounded coin string (DQ1).

## 5. Proposed file split (plan layout, with one addition)

```
TCSlib/Cryptography/ZeroKnowledge.lean                    facade (## Contents)
TCSlib/Cryptography/ZeroKnowledge/Encryption.lean         Def-111.1/a/b, Thm-112.2(.i,.ii), Claim-112.a/b
TCSlib/Cryptography/ZeroKnowledge/Interaction.lean        Def-114.a … Def-116.b
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean  Def-116.1, 117.a/b, Claim-117.c, Def-119.5, 119.e, Def-191.11 (typed)
TCSlib/Cryptography/ZeroKnowledge/Encoding.lean           Inf-4.1 (new; string encodings and their poly-time (de)coders)
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean   Def-117.e, 118.a, Claim-118.b, Prot-118.3, Lem-119.a–d, Prop-118.4, Prot-120.6, Lem-120.a–d, Prop-120.7
TCSlib/Cryptography/ZeroKnowledge/Defs.lean               Def-121.1, 121.2, 122.a, Claim-122.b, Inf-4.4
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK.lean Thm-122.3(.hv,.trunc), Alg-123.4, Lem-123.5, Claim-123.b/d
TCSlib/Cryptography/ZeroKnowledge/Commitment.lean         Def-126.3, Claim-126.a, Alg-127.a, Claim-127.b/c/d, Thm-126.4
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean      Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e/h, Lem-127.f/g, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a/c/d, Lem-129.b
TCSlib/Cryptography/ZeroKnowledge/NP.lean                 Def-124.a, Thm-124.1, Claim-124.d (Claim-124.b/c as hypotheses)
```

`GraphIsomorphism.lean` and `ThreeColoring.lean` are at risk of exceeding 600 lines; split
`ThreeColoring.lean` into `ThreeColoring/Protocol.lean` (protocol, completeness,
soundness) and `ThreeColoring/Simulator.lean` (Alg-128.7 … Claim-129.d) if so.

## 6. Risk notes for the planners

* The chapter's hard core is three "perfect simulation by coin bijection" arguments
  (Claim-123.b, Claim-129.c) and one reduction with an internal restart loop (Claim-129.d);
  everything else is bookkeeping. Budget the fill accordingly.
* Both truncated simulators and the `n`-fold protocols need the Repetition infrastructure
  (Inf-4.3) and DQ1's answer before their PPT side-conditions can be stated.
* Thm-124.1's "every NP language" form is blocked on a string-level Levin reduction to 3COL
  (Claim-124.b/c); state it with the reduction as a hypothesis.
