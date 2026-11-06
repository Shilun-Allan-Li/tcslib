# Quantum Computation and Complexity: Campaign Plan

*Drafted 2026-11-06. Owner: a-gupte. Status: **plan; nothing landed**. Every "decision" below
is provisional until a maintainer closes the matching open question (§8).*

This is the campaign plan required by [`workflow.md`](workflow.md) §1. Read it together with
[`policy.md`](policy.md), the standards every landed file must meet. This file says *what*
gets formalized and in what order. `policy.md` says what the Lean must look like, and
`workflow.md` says how statement phases, audit gates and fills run. Where this plan and
`policy.md` disagree, `policy.md` wins and this plan gets fixed.

## Contents

0. Summary
1. Sources and citation tags
2. Scope and tiers
3. Foundation decisions
4. Architecture and module layout
5. Phases and result inventory
6. Hosts and machine obligations
7. Risks and an honest effort assessment
8. Open design questions (human review required)
9. Getting started: the first three PRs
10. Decision log

---

## 0. Summary

The goal is a quantum computing and quantum complexity layer for TCSlib. It has three parts:

1. **Foundations.** Qubit registers, gates acting on chosen wires, measurement, circuits over
   a fixed finite gate set, polynomial-time uniform circuit families, and the query model.
2. **Pure-math results with no Turing machines.** The early query algorithms, Grover's
   algorithm and its optimality, the polynomial method, the CHSH game and Tsirelson's bound,
   teleportation and no-cloning. These are the cheapest wins and test the foundations.
3. **Complexity classes.** BQP, its error reduction, `P ⊆ BPP ⊆ BQP ⊆ PP ⊆ PSPACE`, then
   PostBQP and QMA. The classical half of these proofs (polynomial-time verifiers, uniformity,
   PSPACE machines) costs the most under TCSlib's rules, so the plan isolates it (FD-8, §6).

No Lean library has quantum complexity classes yet. The Physlib `QuantumInfo` library is the
best source of quantum-information infrastructure, but TCSlib's toolchain (Lean v4.25.0) is
about ten releases behind it. The plan therefore **builds on Mathlib alone, with names that
mirror Physlib** so a later switch is mechanical (FD-1, OQ-1).

## 1. Sources and citation tags

### 1a. The five course texts

Each text is ingested under `blueprint/src/references/` before the first file citing it lands
(policy §2, *Blueprint*; `dataset/INSTRUCTIONS.md`). Licensing is checked first (OQ-2).

| Tag | Text | Version used | Role |
|---|---|---|---|
| **[Wat08]** | J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401 (2008); in *Encyclopedia of Complexity and Systems Science*, Springer, 2009 | arXiv v1 | Definitions of the circuit model, BQP, PQP, QMA and QIP; the theorem numbering for classes (Prop 3, Thms 1, 4–18) |
| **[dW26]** | R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415 | v6 (revision log ends "August'26") | Main textbook for foundations, algorithms, query lower bounds, ch. 13 (complexity), ch. 14 (QMA), chs. 15–17 and 20. Chapter numbers below are **v6's**; they changed between versions. |
| **[Aar10]** | S. Aaronson, *6.845 Quantum Complexity Theory*, MIT OpenCourseWare, Fall 2010, lecture notes | OCW page as of 2026-11-06 | Lecture numbers for BQP and its classical relatives (L4), BBBV (L9), query lower bounds (L10–13), QMA (L14–16), QIP (L17), PostBQP (L18), BQP/qpoly (L20), communication (L21–22) |
| **[Gha20]** | S. Gharibian, *Quantum Complexity Theory*, Paderborn University, winter 2020/21, lecture notes | compiled notes on the course page | BQP-completeness (linear systems), QMA strong error reduction, the quantum Cook–Levin theorem, QCMA and GSCON, QIP via SDPs, BQP vs PH |
| **[Yue22]** | H. Yuen, *COMS 6998: Frontiers of Quantum Complexity and Cryptography*, Columbia, Spring 2022, lecture notes | course page as of 2026-11-06 | Tomography, the Haar measure, the symmetric subspace, shadow tomography, state and unitary synthesis, pseudorandom states, quantum money. Almost entirely Tier C (§2); a few linear-algebra items are Tier B. |

### 1b. Primary sources

Most theorems in [Wat08] and [Aar10] are stated with a citation and no proof. A declaration
whose proof follows a paper cites the paper as well, so these are ingested as their phases
start:

| Tag | Source | Used for |
|---|---|---|
| [AB09] | Arora, Barak, *Computational Complexity*, 2009 (already in TCSlib) | PP, #P, BPP, P-uniformity, the classical containments |
| [NC10] | Nielsen, Chuang, *Quantum Computation and Quantum Information*, 10th anniv. ed. | Standard facts: no-cloning, superdense coding, reversible computation |
| [BV97] | Bernstein, Vazirani, *Quantum complexity theory*, SICOMP 26(5) | BQP ⊆ PSPACE, Bernstein–Vazirani, BPP ⊆ BQP |
| [ADH97] | Adleman, DeMarrais, Huang, *Quantum computability*, SICOMP 26(5) | BQP ⊆ PP |
| [FR99] | Fortnow, Rogers, *Complexity limitations on quantum computation*, JCSS 59(2) | The GapP proof of BQP ⊆ PP; PP^BQP = PP |
| [DJ92] | Deutsch, Jozsa, Proc. R. Soc. A 439 | Deutsch–Jozsa |
| [Sim97] | Simon, SICOMP 26(5) | Simon's problem |
| [Gro96] | Grover, STOC 1996 | Search |
| [BBBV97] | Bennett, Bernstein, Brassard, Vazirani, SICOMP 26(5) | The hybrid lower bound |
| [BBCMW01] | Beals, Buhrman, Cleve, Mosca, de Wolf, JACM 48(4) | The polynomial method |
| [Amb02] | Ambainis, *Quantum lower bounds by quantum arguments*, JCSS 64(4) | The adversary method |
| [Sho97] | Shor, SICOMP 26(5) | QFT, period finding, factoring |
| [CHSH69], [Cir80] | Clauser–Horne–Shimony–Holt; Tsirelson (Cirel'son) | The CHSH game and Tsirelson's bound |
| [Aar05] | Aaronson, *Quantum computing, postselection, and probabilistic polynomial-time*, Proc. R. Soc. A 461 | PostBQP = PP |
| [KSV02] | Kitaev, Shen, Vyalyi, *Classical and Quantum Computation*, AMS 2002 | QMA, the local Hamiltonian problem |
| [MW05] | Marriott, Watrous, *Quantum Arthur–Merlin games*, CC 14(2) | Strong error reduction, QMA ⊆ PP |
| [KKR06] | Kempe, Kitaev, Regev, SICOMP 35(5) | 2-local Hamiltonian (Tier C) |
| [Nay99], [KdW04] | Nayak (random access codes); Kerenidis, de Wolf (2-query LDC lower bound) | Links to `KikuchiLDC` (Tier B) |
| [AG04] | Aaronson, Gottesman, *Improved simulation of stabilizer circuits*, PRA 70 | Gottesman–Knill (Tier B) |

### 1c. Design debts (policy §2, *Design adaptation*)

If a module adapts the design of Physlib `QuantumInfo`, QICLean, inQWIRE LeanQuantum or
duckki/quantum-computing-lean, even with no code transcribed, its `## References` section names
the project, the module, the commit consulted and the license. If we only look at their code
for comparison, the consultation still goes in this file's decision log (§10).

## 2. Scope and tiers

| Tier | Meaning | Contents |
|---|---|---|
| **A: core** | Mandatory. The campaign closes when Tier A is proved. | Q0 (classical prerequisites), Q1 (foundations), Q2 (circuits), the Q3 core (DJ, BV, Simon, Grover, hybrid bound, polynomial-method degree lemma), Q4 (BQP, error reduction, `P ⊆ BPP ⊆ BQP ⊆ PP ⊆ PSPACE`, `BQP ⊆ EXP`), the Q5 core (CHSH, magic square) |
| **B: extended** | Planned, after Tier A gates close. Each item can be dropped without affecting anything else. | Tsirelson; adversary method; `OR` needs Ω(√N) queries; PQP = PP; PostBQP = PP; the BQP subroutine theorem; QMA (definitions, weak and strong error reduction, Jordan's lemma, QMA ⊆ PP, k-LH ∈ QMA); QFT and phase estimation; Shor's period finding; Gottesman–Knill; mixed states and Nayak's bound; symmetric-subspace facts from [Yue22] L4 |
| **C: deferred** | Research-scale. Recorded so scope stays honest. Not planned. | Solovay–Kitaev [Wat08 Thm 1]; QMA-hardness of k-LH [Wat08 Thm 8] and 2-local [KKR06]; QIP ⊆ EXP, QIP(3), QSZK, QMAM = QIP [Wat08 Thms 11–15]; QIP = PSPACE; BQP/qpoly ⊆ PP/poly [Wat08 Thm 16]; QMA/qpoly [Thm 17]; space-bounded classes [Thm 18]; bounded-depth circuits [§VII.3]; the collision lower bound [Aar10 L12–13]; BQP vs PH oracle separation [Aar10 L14, Gha20]; boson sampling; GSCON; HHL and BQP-completeness of linear systems [dW26 ch. 10, Gha20]; Hamiltonian simulation [dW26 ch. 9]; quantum walks [dW26 ch. 8]; non-abelian HSP; tomography, shadow tomography, state and unitary synthesis, PRS and quantum money [Yue22]; fault tolerance [dW26 ch. 21] |

## 3. Foundation decisions

These are the definitional conventions, and they are where audits bite (`workflow.md` §1).
Each one names its open question in §8.

**FD-1. No new Lake dependency (OQ-1).** Build on Mathlib at TCSlib's pin. Checked
2026-11-06 against Lean v4.25.0 and the pinned Mathlib: `Matrix.unitaryGroup`,
`Matrix.PosSemidef`, `Matrix.kroneckerMap`, `Matrix.trace`, `EuclideanSpace`,
`Matrix.toEuclideanLin`, `GaussianInt` (in `Mathlib.NumberTheory.Zsqrtd.GaussianInt`) and
`GenContFract` all elaborate. Where an object exists in Physlib `QuantumInfo` (`MState`,
`CPTPMap`, `POVM`, `HermitianMat`, `Ket`), our version takes the same name and the same
field layout. Reason: the Physlib toolchain is v4.35.0, so adding it means bumping all of
TCSlib (and PFR). That is a maintainer decision, and this campaign should not wait on it.

**FD-2. Registers and states.** An `n`-qubit basis state is `Fin n → Bool`. A state is
`Quantum.Ket n := EuclideanSpace ℂ (Fin n → Bool)`, an operator is
`Matrix (Fin n → Bool) (Fin n → Bool) ℂ`, and a unitary is an element of
`Matrix.unitaryGroup`. We use `Bool` and not `Fin 2` because TCSlib's languages, circuits
and Fourier analysis all use `Bool`. The existing `ErrorCorrectingCodes/QuantumHamming.lean`
uses `Fin n → Fin 2`; its migration is OQ-6.

**FD-3. Gates act on wires through an injection, not Kronecker products.** For a `k`-qubit
gate `U` and an embedding `w : Fin k ↪ Fin n`, `applyOn w U` is defined entrywise:
`⟨y| applyOn w U |x⟩ = U (y ∘ w) (x ∘ w)` when `x` and `y` agree off the range of `w`, and
`0` otherwise. This avoids reordering tensor factors, which is where formal quantum
libraries spend most of their effort. Phase Q1 proves the bridge lemmas: unitarity is
preserved; gates on disjoint wires commute; and on adjacent wires `applyOn` agrees with
`Matrix.kroneckerMap` up to the canonical reindexing. They land as sanity theorems
(`workflow.md` §3).

**FD-4. The official gate set is [Wat08 §III.2]: Toffoli, Hadamard and the phase gate
`P = diag(1, i)` (OQ-8).** Circuits are generic in a gate alphabet `G` with a semantics
`G → Σ k, unitary on k qubits`. Query algorithms (Q3) may use any unitaries. Complexity
classes (Q4, Q6) are defined over Watrous's set. In this set every matrix entry has real
and imaginary parts in `{0, ±1/2, ±1}` after scaling by `√2` per Hadamard, which is exactly
what the path-sum proof of `BQP ⊆ PP` needs [Wat08 §IV.5]. Ancillas are extra wires that
start in `|0⟩`: this is the unitary purification of [Wat08 §III.3]. Erasure gates and
general (mixed-state) circuits are left out of the core (Q8). [Wat08 Thm 1], which makes the
choice of gate set irrelevant, is Tier C, so each class's docstring records this deviation.

**FD-5. Acceptance (OQ-5).** `accProb Q x = ‖Π₁ (U_Q |x, 0^m⟩)‖²`, where `Π₁` projects the
designated output wire onto `|1⟩`. Probabilities are real numbers. Outcome `1` means
*accept*, following [dW26], [Aar10] and [AB09]. [Wat08 §IV.1] uses the opposite labels, so
the deviation is noted wherever [Wat08] is cited.

**FD-6. Uniformity follows `BoolCircuit.DAGCircuitFamily.IsPUniform`.** A family
`Q : ℕ → QCircuit G` is P-uniform if some `f` with `Complexity.PolyTimeComputable f` sends
`1ⁿ` to `(Q n).encode`. This is the shorthand form of [Wat08 Def 2], where the family is
indexed by input length. The circuit `Q n` has `n` input wires and `anc n` ancilla wires. A
lemma `IsPUniform.isPolySize` (mirroring the Boolean one) gives polynomial size and ancilla
count for free. `QCircuit.encode` is a fixed, injective, prefix-free description over `Bool`.

**FD-7. Languages first, promise problems where needed (OQ-4).** BQP, PP and PostBQP are
predicates on `Language Bool`, so they compose with the existing `P`, `BPP`, `PP` and
`PSPACE`. The promise layer (`PromiseProblem := yes and no sets, disjoint`) arrives in Q0
because QMA and the local Hamiltonian problem are intrinsically promise problems. The
language version of each class is its promise version with `no = yesᶜ`, by a lemma rather
than by definition.

**FD-8. Classical-side arguments against an abstract `VerifierModel` (precedent:
`Randomized.bpp_subset_sigma2 (hMaj : ClosedUnderMajority E)`).** PP is
`Counting.InPP (E : VerifierModel) L`, mirroring `Randomized.InBPP`. Quantum-to-classical
containments such as `BQP ⊆ PP` are stated for any `E` with named closure hypotheses
(gap sums, products, polynomial-time preprocessing). Each closure is discharged for
`Randomized.polyTimeModel` in a separate file. This keeps the quantum argument (path sums,
linear algebra) apart from the machine construction, each with its own gate and fill batch,
and nothing on the quantum side touches `FinTM`.

**FD-9. The query model.** An `N`-bit input `z : Fin N → Bool` is accessed through the
oracle `O_z |i, b, w⟩ = |i, b ⊕ zᵢ, w⟩`, with the phase oracle as a derived lemma. A
`T`-query algorithm is a list of `T + 1` input-independent unitaries interleaved with
`O_z`. `QQ_ε(f)` is the least such `T`. Classical query models for the separations
(deterministic and randomized) reuse `BooleanAnalysis/DecisionTree.lean` wherever it fits.

**FD-10. Exact semantics.** Amplitudes are computed in `ℂ`. The *path-sum lemma* (Q2) shows
that every amplitude of a Watrous circuit with `h` Hadamards equals `(1/√2)^h` times a sum
of terms in `{±1, ±i}` indexed by `h`-bit paths, each term computable from the path. That
lemma is the only bridge from quantum circuits to counting classes, and its statement is
audit-critical.

**FD-11. ℝ against ℚ (OQ-7).** `Randomized.randProb` takes values in `ℚ`. Quantum acceptance
probabilities take values in `ℝ`. The containment `BPP ⊆ BQP` needs a cast lemma
(`(randProb m A : ℝ) = uniform-measure probability`), which Q0 proves once.

**FD-12. The model registry.** `QCircuit` defines a model of computation, so it may sit at
the root namespace provided it is registered in `TCSlib/ComputationalModels.lean`, with its
conversion `BoolCircuit.DAGCircuit.toReversible` listed under *Conversions* (policy §1,
*model registry exception*).

## 4. Architecture and module layout

The layout follows policy §1: facades with `## Contents`, files of 150–600 lines, definition
files separate from theorem files, and every facade exported from `TCSlib.lean`.

```
TCSlib/Quantum.lean                         facade (area: Quantum, namespace `Quantum`)
TCSlib/Quantum/Basic.lean                   facade
  Basic/Register.lean      Ket, basisKet, Op, inner products, tensor of kets
  Basic/Gates.lean         H, X, Z, P, CNOT, Toffoli; unitarity; HPPH = X [Wat08 Fig 4]
  Basic/ApplyOn.lean       FD-3: applyOn, locality and commutation lemmas, Kronecker bridge
  Basic/Measure.lean       Born rule, single-qubit measurement, accProb
  Basic/Protocols.lean     no-cloning, teleportation, superdense coding
TCSlib/Quantum/Circuits.lean                facade
  Circuits/Basic.lean      QCircuit G n m, eval, size, unitarity of eval
  Circuits/Watrous.lean    the gate set of FD-4
  Circuits/Encode.lean     encode/decode, injectivity
  Circuits/Uniform.lean    IsPUniform, isPolySize
  Circuits/Reversible.lean DAGCircuit → Toffoli circuit with uncomputation
  Circuits/PathSum.lean    FD-10
  Circuits/Counting.lean   most functions need exponential size [dW26 §13.1]
TCSlib/Quantum/Query.lean                   facade
  Query/Basic.lean, Query/DeutschJozsa.lean, Query/BernsteinVazirani.lean,
  Query/Simon.lean, Query/Grover.lean, Query/AmplitudeAmplification.lean,
  Query/Hybrid.lean, Query/Polynomial.lean, Query/Adversary.lean (B)
TCSlib/Quantum/Nonlocal.lean                facade
  Nonlocal/CHSH.lean, Nonlocal/Tsirelson.lean (B), Nonlocal/MagicSquare.lean
TCSlib/Quantum/MixedStates.lean             (Tier B) MState, POVM, partial trace, Physlib names
TCSlib/Quantum/Algorithms.lean              (Tier B) QFT, PhaseEstimation, Shor/*, AbelianHSP
TCSlib/Complexity/Promise.lean              facade; Promise/Basic.lean
TCSlib/Complexity/Counting.lean             facade (namespace `Counting`)
  Counting/PP.lean         InPP E, gapCount, closure predicates
  Counting/GapP.lean       GapP closure under sums, products and negation
  Counting/Inclusions.lean NP ⊆ PP, BPP ⊆ PP, PP closed under complement
  Counting/PolyTime.lean   closures discharged for polyTimeModel
  Counting/PSPACE.lean     PP ⊆ PSPACE (machine work; §6)
TCSlib/Complexity/Quantum.lean              facade (namespace `QuantumComplexity`)
  Quantum/BQP.lean         InBQPWith a b, InBQP, promise version
  Quantum/ErrorReduction.lean
  Quantum/Classical.lean   P ⊆ BQP, BPP ⊆ BQP, closure under complement
  Quantum/UpperBounds.lean BQP ⊆ PP, BQP ⊆ PSPACE, BQP ⊆ EXP
  Quantum/PostBQP.lean (B), Quantum/Subroutine.lean (B)
  Quantum/QMA/Basic.lean, QMA/WeakAmplify.lean, QMA/Jordan.lean, QMA/StrongAmplify.lean,
  QMA/PP.lean, QMA/LocalHamiltonian.lean   (all B)
```

The blueprint is late-bound (`workflow.md` §5): `blueprint/src/chapter/Quantum/` is
generated at phase boundaries and never written by hand ahead of the Lean.

## 5. Phases and result inventory

Each phase lands first as a **sorry-skeleton**: definitions plus statements, with a proof
sketch under every `sorry`, gated by an external audit before any fill (`workflow.md` §2–3).
Difficulty uses the blueprint's 1–5 scale; S/M/L is the expected size of the fill.

Dependency order: **Q0 ∥ Q1 → Q2 → (Q3 ∥ Q4 ∥ Q5) → Q6 → Q7**. Q3 and Q5 need only Q1.

### Q0. Classical prerequisites (`Complexity/Promise`, `Complexity/Counting`)

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q0.1 | `PromiseProblem`; promise versions of P and BPP; language ↔ promise lemmas | [Wat08 §II.1] | 1 / S | A |
| Q0.2 | `InPP E`: `x ∈ L ↔ randProb[M x r] > 1/2` | [AB09 ch. 17], [Wat08 §IV.5] | 1 / S | A |
| Q0.3 | `gapCount`; GapP closure under `+`, `·`, negation and polynomial-time preprocessing, as hypotheses on `E` | [FR99 §2], [Wat08 §IV.5] | 2 / M | A |
| Q0.4 | `PP ↔ ∃ gap function g, x ∈ L ↔ g x > 0` | [FR99] | 2 / S | A |
| Q0.5 | `NP ⊆ PP`, `BPP ⊆ PP` | [AB09 ch. 17] | 2 / S | A |
| Q0.6 | PP is closed under complement (the tie-breaking shift) | [AB09 ch. 17] | 3 / M | A |
| Q0.7 | The Q0.3 closures hold for `polyTimeModel` | — | 3 / L (machine-adjacent; §6) | A |
| Q0.8 | `PP ⊆ PSPACE` | [AB09 ch. 17] | 4 / L (host HQ-1) | A |
| Q0.9 | `randProb` cast lemma (FD-11) | — | 1 / S | A |

### Q1. Quantum foundations (`Quantum/Basic`)

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q1.1 | Registers, kets, basis kets, operators, tensors of kets | [dW26 §1.2–1.3, App. A] | 1 / M | A |
| Q1.2 | Gates and their unitarity; `X = HPPH`, CNOT from Toffoli and an ancilla | [dW26 §1.4], [Wat08 §III.2, Fig 4] | 1 / S | A |
| Q1.3 | `applyOn` (FD-3) and its lemmas | — | 3 / M (**the risk item**, R4) | A |
| Q1.4 | Born rule: outcome probabilities sum to 1; partial measurement of one qubit | [dW26 §1.2.2] | 2 / S | A |
| Q1.5 | No-cloning (linearity version) | [NC10 Box 12.1] | 1 / S | A |
| Q1.6 | Teleportation and superdense coding are correct | [dW26 §1.5], [NC10 §2.3] | 2 / M | A |

### Q2. Circuits (`Quantum/Circuits`)

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q2.1 | `QCircuit G n m`, `eval`, `size`; `eval` is unitary | [Wat08 §III.1], [dW26 §2.1.2] | 2 / M | A |
| Q2.2 | Watrous gate set, encoding, decoding, injectivity | [Wat08 §III.2] | 2 / M | A |
| Q2.3 | `IsPUniform` and `isPolySize` | [Wat08 Def 2] | 2 / S | A |
| Q2.4 | Reversible simulation: every `DAGCircuit` has a Toffoli circuit computing `|x,0,0⟩ ↦ |x, f(x), 0⟩` (Bennett-style uncomputation), with linear size, and the compilation is polynomial-time on encodings | [Wat08 §IV.3], [NC10 §3.2.5] | 3 / L | A |
| Q2.5 | Path-sum lemma (FD-10) | [Wat08 §IV.5], [dW26 §13.3] | 3 / M | A |
| Q2.6 | Most Boolean functions need circuits of exponential size | [dW26 §13.1] | 3 / M | A |

### Q3. Query complexity and algorithms (`Quantum/Query`); pure math

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q3.1 | Query model (FD-9); phase-oracle lemma | [dW26 §2.3] | 2 / S | A |
| Q3.2 | Deutsch–Jozsa: 1 exact query; deterministic algorithms need `N/2 + 1` | [dW26 §2.4.1], [DJ92] | 2 / M | A |
| Q3.3 | Bernstein–Vazirani: 1 query recovers `s` (through `BooleanAnalysis.chiS`) | [dW26 §2.4.2], [BV97] | 2 / S | A |
| Q3.4 | Simon: the quantum step samples uniformly from `s^⊥`; `O(n)` queries suffice with high probability; classical randomized algorithms need `Ω(√2ⁿ)` | [dW26 ch. 3], [Sim97] | 3 / L | A |
| Q3.5 | Grover: the exact rotation analysis; `⌊π/4 √N⌋` queries find the marked item with probability `≥ 1 − O(1/N)` (the exact constant fixed at statement time from [dW26 §7.2]) | [dW26 §7.2], [Gro96] | 3 / M | A |
| Q3.6 | Amplitude amplification | [dW26 §7.3] | 3 / M | B |
| Q3.7 | Hybrid argument: search needs `Ω(√N)` queries | [Aar10 L9], [BBBV97] | 3 / M | A |
| Q3.8 | Polynomial method: after `T` queries, the acceptance probability is a real multilinear polynomial in `z` of degree `≤ 2T` | [dW26 §11.2], [BBCMW01] | 3 / M | A |
| Q3.9 | `OR` needs `Ω(√N)` queries (symmetrization plus Markov's inequality for polynomials) | [dW26 §11.2] | 4 / L (R2: Markov's inequality may be missing from Mathlib) | B |
| Q3.10 | Basic adversary method; search and `OR` lower bounds | [dW26 §11.3], [Amb02] | 4 / L | B |

### Q4. BQP and its classical bounds (`Complexity/Quantum`)

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q4.1 | `InBQPWith a b`, `InBQP = InBQPWith (2/3) (1/3)`, promise version | [Wat08 §IV.1], [dW26 §13.2] | 2 / S | A |
| Q4.2 | Error reduction: `BQP(a, b) = BQP = BQP(1 − 2^{−q}, 2^{−q})` (parallel copies, majority; reuses `Randomized.majority_error_le`) | [Wat08 Prop 3] | 4 / L | A |
| Q4.3 | `P ⊆ BQP` and `BPP ⊆ BQP` (Q2.4 plus Hadamard coins; uses `Language.exists_isPUniform_of_mem_P`) | [Wat08 §IV.3], [BV97] | 3 / M | A |
| Q4.4 | BQP is closed under complement | [dW26 §13.2] | 1 / S | A |
| Q4.5 | `BQP ⊆ PP` for any `E` with the Q0.3 closures; then for `polyTimeModel` | [Wat08 Thm 5], [ADH97], [FR99] | 4 / L | A |
| Q4.6 | `BQP ⊆ PSPACE` (from Q4.5 and Q0.8) and `BQP ⊆ EXP` | [dW26 §13.3], [BV97] | 2 / S given Q0.8 | A |
| Q4.7 | `PQP = PP` | [Wat08 Thm 7] | 4 / L | B |
| Q4.8 | BQP subroutine theorem, `BQP^BQP = BQP` | [Wat08 Thm 4, Cor 5] | 4 / L (needs oracle circuits) | B |
| Q4.9 | `PostBQP = PP` (`⊆` by the path-sum argument; `⊇` by Aaronson's construction) | [Aar05], [Aar10 L18] | 4 / XL | B |
| Q4.10 | `PP^BQP = PP` | [Wat08 Thm 6], [FR99] | 5 / XL | C |

### Q5. Nonlocality and information (`Quantum/Nonlocal`, `Quantum/MixedStates`)

| ID | Statement | Source | Difficulty / size | Tier |
|---|---|---|---|---|
| Q5.1 | CHSH: classical value `3/4`; the EPR strategy wins with probability `cos²(π/8)` | [dW26 §17.2], [CHSH69] | 2 / M | A |
| Q5.2 | Tsirelson's bound: every quantum strategy wins with probability at most `cos²(π/8)` | [Cir80], [dW26 §17.2] | 3 / M | B |
| Q5.3 | Magic square: no perfect classical strategy; a perfect quantum strategy exists | [dW26 §17.3] | 2 / M | A |
| Q5.4 | Mixed states, POVMs, partial trace (Physlib names, FD-1) | [dW26 §15.1] | 2 / M | B |
| Q5.5 | Nayak's bound for quantum random access codes; then the 2-query LDC lower bound, linked to `KikuchiLDC` | [dW26 §15.2–15.3], [Nay99], [KdW04] | 5 / XL (needs von Neumann entropy; OQ-9) | B |
| Q5.6 | Symmetric subspace: its dimension and the projector as an average over permutations | [Yue22 L4] | 3 / M | B |
| Q5.7 | Distributed Deutsch–Jozsa protocol (upper bound only); quantum fingerprinting using the codes in `ErrorCorrectingCodes` | [dW26 §16.3, §16.6] | 3 / M | B |

### Q6. QMA (`Complexity/Quantum/QMA`); Tier B

| ID | Statement | Source | Difficulty / size |
|---|---|---|---|
| Q6.1 | `QMA(a, b)`, `QCMA`; `NP ⊆ QCMA ⊆ QMA`, `BQP ⊆ QMA` | [Wat08 §V.1], [dW26 §14.1], [Gha20] | 2 / M |
| Q6.2 | Weak error reduction by parallel repetition (the largest eigenvalue of a tensor product of acceptance operators is the product of the largest eigenvalues) | [KSV02], [Wat08 §V.3] | 3 / M |
| Q6.3 | Jordan's lemma for two projectors | [MW05], [Gha20] | 4 / L |
| Q6.4 | Strong error reduction | [Wat08 Thm 10], [MW05] | 4 / L |
| Q6.5 | `QMA ⊆ PP` | [Wat08 §V.4], [MW05] | 4 / L |
| Q6.6 | k-local Hamiltonian problem (a promise problem); `k-LH ∈ QMA` | [dW26 §14.2], [KSV02], [Gha20] | 4 / L |
| Q6.7 | QMA-hardness of 5-LH (Feynman–Kitaev clock construction) | [dW26 §14.3], [KSV02] | 5 / XL (Tier C) |

### Q7. Algorithms (`Quantum/Algorithms`); Tier B

| ID | Statement | Source | Difficulty / size |
|---|---|---|---|
| Q7.1 | QFT is unitary; its `O(n²)` circuit is correct | [dW26 §4.4–4.5] | 3 / M |
| Q7.2 | Phase estimation | [dW26 §4.6] | 4 / L |
| Q7.3 | Factoring reduces to period finding (classical, using `ClassP/BinaryArith`) | [dW26 §5.2] | 3 / M |
| Q7.4 | Shor's period finding succeeds with probability `Ω(1/log log N)`; recovery by continued fractions (`GenContFract`) | [dW26 §5.3–5.4], [Sho97] | 5 / XL |
| Q7.5 | Abelian hidden subgroup problem | [dW26 §6.2] | 4 / L |
| Q7.6 | Gottesman–Knill: Clifford circuits simulated in polynomial time (connects to the stabilizer codes in `ErrorCorrectingCodes`) | [dW26 §20.3], [AG04] | 4 / L |

### Phase gates and fill epochs

| Statement phase | Content | Gate |
|---|---|---|
| P1 | Q0.1–Q0.6, Q0.9, Q1 | `quantum-phase1` |
| P2 | Q2, Q3 Tier A | `quantum-phase2` |
| P3 | Q4 Tier A, Q5 Tier A | `quantum-phase3` |
| P4+ | Tier B, one gate per section | per section |

| Fill epoch | Content | Why this order |
|---|---|---|
| E1 | Q1, Q3, Q5 core: pure math, no machines | Tests FD-3 early (R4); quick, visible wins |
| E2 | Q0 counting, Q2.5, Q4.1–Q4.5 against an abstract `E` | Settles the audit-critical statements while `polyTimeModel` work is still pending |
| E3 | Q0.7, Q0.8, Q2.4's polynomial-time compiler, `polyTimeModel` instances | The machine work, behind the hosts of §6 |

## 6. Hosts and machine obligations

This section applies policy §1 (*Hosts come first*) and `machine-library-design.md` §14.

* **HQ-1, a counting certificate enumerator** for `PP ⊆ PSPACE` (Q0.8).
  `Complexity.NP_subset_PSPACE` already cycles through certificates with a fixed-width
  increment (`b2b_host`, using `counterLoopTM`, `phaseHostTM` and `LogProg.cleanTM_run`).
  PP needs the same loop plus a polynomial-width binary counter. Because that makes it a
  second consumer, policy requires the enumerator to be **harvested into a public host**
  (statement gate first) before Q0.8 is briefed. The ARM route (H7, `arm_decides_pspace`,
  as for `TQBF_mem_PSPACE`) is the alternative; the host's gate chooses between them.
* **Not hosts: polynomial-time functions on descriptions.** Q0.7 needs "the sign of path
  `r` through circuit description `c` on input `x`" to be polynomial-time, and Q2.4 needs
  the reversible compiler to be polynomial-time on encodings. Both are plain functions on
  `List Bool`. The plan proves them through the polynomial-time closure algebra
  (`PolyTimeComputable.comp`, pairing, the `ClassP/BinaryArith` primitives) and, where
  that is enough, through the Karp reduction to `BoolCircuit.CVAL` (`CVAL_mem_P`) used by
  `PUniformP.lean`. If any of them turns out to need an interpreter loop, that is an
  escalation (`workflow.md` §4 rule 4) and the host goes through its own gate.
* No quantum file builds a machine. FD-8 keeps every `FinTM` argument in `Counting/`,
  `Circuits/Uniform.lean` and the `polyTimeModel` instance files.

## 7. Risks and an honest effort assessment

* **R1. The classical plumbing dominates.** In the Arora–Barak campaign the machine
  constructions, not the mathematics, set the pace. Here Q0.7, Q0.8 and Q2.4 carry that
  risk. Mitigation: FD-8, and epoch E3 runs last, so a delay there blocks nothing else.
* **R2. Real analysis.** Grover's angles are routine. Markov's inequality for polynomials
  (Q3.9), Shor's probability bound (Q7.4) and Solovay–Kitaev (Tier C) are not.
  Mitigation: these sit in Tier B or C, and Q3.9 checks Mathlib before it is briefed.
* **R3. Concentration.** Error reduction needs a Chernoff/Hoeffding bound over `ℝ`.
  `Randomized.majority_error_le` and `iid_bernoulli_avg_concentration` already provide it
  for i.i.d. Bernoulli trials. The remaining work is showing that measuring parallel copies
  on disjoint registers produces i.i.d. outcomes, which is a Q1/Q2 lemma.
* **R4. Ergonomics of `applyOn`.** If FD-3's definition is awkward, every circuit proof
  suffers. Mitigation: Q1.3 lands first with sanity theorems (Grover's diffusion operator,
  teleportation) exercising it before Q2 is gated.
* **R5. Version drift.** A Mathlib bump in the middle of the campaign moves names.
  Mitigation: precise imports; Physlib-compatible names; no dependency until OQ-1 closes.
* **R6. Statement subtleties.** The family's indexing, ancilla counts, the acceptance
  convention, `ℚ` against `ℝ`, and promise against language are exactly where audits find
  majors. FD-4 to FD-7 and FD-11 exist to put these on the record before P1's gate.

**Effort.** The Tier A pure-math part (Q1, Q3 core, Q5 core) is comparable in size to one of
TCSlib's existing self-contained topics such as `LearningTheory/Hedge` or
`ErrorCorrectingCodes`. The Tier A complexity part (Q0, Q2, Q4) is comparable to a chapter
of the Arora–Barak campaign, and most of that size comes from E3. Tier B is several times
larger again. Each item in it is independent, so it can be taken one at a time. Tier C is
out of scope for this campaign.

## 8. Open design questions (human review required)

These follow the `workflow.md` §1 rule: audit rounds verify them but never decide them. Each
question records the provisional choice and stays open until a maintainer closes it. Once
accepted, the stubs move into `backlog.md`.

| ID | Question | Provisional choice |
|---|---|---|
| OQ-1 | Take a dependency on Physlib `QuantumInfo` (which needs a Mathlib/Lean/PFR bump), or self-build with Physlib-compatible names? | Self-build now; revisit at the next Mathlib bump, before Tier B's mixed-state work (Q5.4–Q5.5, Q6) |
| OQ-2 | May the arXiv-licensed PDFs ([Wat08], [dW26]) and the CC BY-NC-SA OCW notes ([Aar10]) be ingested into `blueprint/src/references/`? What about [Gha20] and [Yue22], whose licenses are not stated? | Ingest the converted `.md` pairs, as for the existing `PhysRev*` and `arXiv.*` references, subject to the maintainer's licensing check |
| OQ-3 | Area and namespaces: `TCSlib/Quantum` (namespace `Quantum`) for models plus `TCSlib/Complexity/Quantum` (namespace `QuantumComplexity`) for classes? | Yes |
| OQ-4 | Promise problems first-class from the start, or only from Q6? | Defined in Q0; BQP stated on languages, with a promise version |
| OQ-5 | Acceptance outcome `1` (de Wolf, Aaronson, AB09) or `0` (Watrous)? | `1`, with a deviation note wherever [Wat08] is cited |
| OQ-6 | Migrate `ErrorCorrectingCodes/QuantumHamming.lean` (`Fin n → Fin 2`, its own Pauli strings) onto `Quantum/Basic`? | Not in this campaign; a bridge lemma (`Fin 2 ≃ Bool`) once Q1 lands, migration queued in `backlog.md` |
| OQ-7 | `ℝ`-valued quantum probabilities next to `ℚ`-valued `randProb`? | Keep both, with the Q0.9 cast lemma |
| OQ-8 | Official gate set: Watrous's {Toffoli, H, P}, {Toffoli, H} (real amplitudes), or gate-set-generic classes? | Watrous's set; gate-set independence waits for Solovay–Kitaev (Tier C) |
| OQ-9 | Mixed states and entropy: our own minimal layer or Physlib's? | Decided with OQ-1 before Q5.4 |
| OQ-10 | Where do campaign records (this plan, packs, briefs) live, now that `campaign/`, `audits/` and `briefs/` are kept off `main`? | This file on the campaign branch; the maintainer decides what reaches `main` |

## 9. Getting started: the first three PRs

1. **This plan.** Open it as a PR (or an issue) so a maintainer can rule on OQ-1, OQ-2,
   OQ-3 and OQ-10 before any Lean lands.
2. **References.** Ingest [Wat08] and [dW26], plus [Aar10] once OQ-2 allows:
   `python3 scripts/sources.py add Wat08=<pdf>` and the same for `dW26`. The `add` step
   runs paid `claude -p` matching stages; `python3 scripts/dataset_pipeline.py --estimate`
   shows the cost first.
3. **Phase P1 skeleton.** `Complexity/Promise`, `Complexity/Counting/{PP,GapP,Inclusions}`
   and `Quantum/Basic/*`, as statements with a proof sketch under every `sorry`, plus the
   FD-3 sanity theorems. Verify with `zsh scripts/lean_check.sh <file>` on each file,
   `python3 scripts/style_lint.py` and the policy review checklist, then write the
   `quantum-phase1` audit pack (`workflow.md` §3).

## 10. Decision log

Append-only. A superseded row is marked **Superseded** in place, never deleted.

| Date | Decision / event | By |
|---|---|---|
| 2026-11-06 | Plan drafted from [Wat08], [dW26] v6, [Aar10], [Gha20] and [Yue22]. Tiers A/B/C set (§2). | a-gupte (with Claude) |
| 2026-11-06 | External libraries consulted for comparison only, nothing taken: Physlib `QuantumInfo` (Lean v4.35.0, Apache-2.0); Timeroot/Lean-QuantumInfo (archived into Physlib, MIT); LionSR/QICLean (v4.36.0-rc1, Apache-2.0, contains `sorry`s and axioms); inQWIRE/LeanQuantum (v4.30.0-rc2, MIT); duckki/quantum-computing-lean (v4.33.1). None has quantum complexity classes. | a-gupte (with Claude) |
| 2026-11-06 | FD-1 to FD-12 adopted provisionally; OQ-1 to OQ-10 opened. | a-gupte (with Claude) |
| 2026-11-06 | Mathlib APIs FD-1 relies on checked to elaborate at the pin (Lean v4.25.0). | a-gupte (with Claude) |
