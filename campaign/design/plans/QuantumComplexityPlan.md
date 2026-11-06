# Quantum Computation and Complexity: Campaign Plan

*Drafted 2026-11-06. Owner: a-gupte. Status: **plan; nothing landed**. Every "decision" below
is provisional until a maintainer closes the matching open question (§8).*

This is the campaign plan required by [`workflow.md`](../../../workflow.md) §1. Read it together with
[`policy.md`](../../../policy.md), the standards every landed file must meet. This file says *what*
gets formalized and in what order. `policy.md` says what the Lean must look like, and
`workflow.md` says how statement phases, audit gates and fills run. Where this plan and
`policy.md` disagree, `policy.md` wins and this plan gets fixed.

**Where the records live.** This campaign follows the Arora–Barak chapters 3–4 precedent. Its
records (this plan, audit gates, fill briefs, the backlog) live under `campaign/` on the
long-lived branch `quantum/campaign`, and they never reach `main`. Only Lean code (and the
blueprint and reference files that go with it) is merged to `main`, through PRs. See
`campaign/README.md` (OQ-10).

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
9. How this plan meets policy.md
10. Getting started: the first three PRs
11. Decision log

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
best source of quantum-information infrastructure, and it already has kets, single-qubit
gates, mixed states, POVMs, channels and entropy. It has no circuit model: no gates applied to
chosen wires of an `n`-qubit register, no circuits over a gate set, no uniform families. Two
things stand between TCSlib and a Physlib dependency. TCSlib's toolchain (Lean v4.25.0) is
about ten releases behind. And Physlib's pure-state basics alone pull in 38 support modules
(about 20,000 lines) written for the newer Lean module system, so copying a few files is not
an option either. The plan therefore splits the work (FD-1, OQ-1):

* **Tier A** uses a thin layer on Mathlib for the overlap (kets, standard gates, the Born
  rule: a few hundred lines). It copies Physlib's *design*, so after a future Mathlib bump the
  overlapping definitions can be deleted and replaced by Physlib's.
* **Tier B's quantum information** (mixed states, POVMs, channels, entropy) is **not**
  rebuilt here. It waits for the Mathlib bump and a Physlib dependency.

## 1. Sources and citation tags

### 1a. The five course texts

Each text is ingested under `blueprint/src/references/` before the first file citing it lands
(policy §2, *Blueprint*; `dataset/INSTRUCTIONS.md`). The procedure is the one used for [AB09]
(OQ-2): the PDF stays local; `scripts/sources.py add <TAG>=<pdf>` produces `<name>.raw.md`
(page-by-page text extraction, with the PDF's SHA-256 in its header) and `<name>.md` (the
validated version, anchored to PDF pages); those two files and the tag's entry in
`blueprint/src/references/sources.json` are committed. No PDF is committed.

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
for comparison, the consultation still goes in this file's decision log (§11).

**This applies to FD-2 from the start.** The `Quantum/Basic` modules adopt Physlib's design,
so each one's `## References` carries:

```
* [Physlib] leanprover-community/physlib, `QuantumInfo/States/Pure/Braket.lean` and
  `QuantumInfo/States/Pure/Qubit.lean` (authors A. Meiburg, R. Soldati and contributors),
  commit cdfa6094901b8956a378151f64088bcf5a5f8bcb, Apache-2.0. Design adapted, no code
  transcribed: the `Ket` structure, `Qubit := Fin 2`, the `𝐔[d]` notation, gate names.
```

## 2. Scope and tiers

| Tier | Meaning | Contents |
|---|---|---|
| **A: core** | Mandatory. The campaign closes when Tier A is proved. | Q0 (classical prerequisites), Q1 (foundations), Q2 (circuits), the Q3 core (DJ, BV, Simon, Grover, hybrid bound, polynomial-method degree lemma), Q4 (BQP, error reduction, `P ⊆ BPP ⊆ BQP ⊆ PP ⊆ PSPACE`, `BQP ⊆ EXP`), the Q5 core (CHSH, magic square) |
| **B: extended** | Planned, after Tier A gates close. Each item can be dropped without affecting anything else. | Tsirelson; adversary method; `OR` needs Ω(√N) queries; PQP = PP; PostBQP = PP; the BQP subroutine theorem; QMA (definitions, weak and strong error reduction, Jordan's lemma, QMA ⊆ PP, k-LH ∈ QMA); QFT and phase estimation; Shor's period finding; Gottesman–Knill; mixed states and Nayak's bound; symmetric-subspace facts from [Yue22] L4 |
| **C: deferred** | Research-scale. Recorded so scope stays honest. Not planned. | Solovay–Kitaev [Wat08 Thm 1]; QMA-hardness of k-LH [Wat08 Thm 8] and 2-local [KKR06]; QIP ⊆ EXP, QIP(3), QSZK, QMAM = QIP [Wat08 Thms 11–15]; QIP = PSPACE; BQP/qpoly ⊆ PP/poly [Wat08 Thm 16]; QMA/qpoly [Thm 17]; space-bounded classes [Thm 18]; bounded-depth circuits [§VII.3]; the collision lower bound [Aar10 L12–13]; BQP vs PH oracle separation [Aar10 L14, Gha20]; boson sampling; GSCON; HHL and BQP-completeness of linear systems [dW26 ch. 10, Gha20]; Hamiltonian simulation [dW26 ch. 9]; quantum walks [dW26 ch. 8]; non-abelian HSP; tomography, shadow tomography, state and unitary synthesis, PRS and quantum money [Yue22]; fault tolerance [dW26 ch. 21] |

## 3. Foundation decisions

These are the definitional conventions, and they are where audits bite (`workflow.md` §1).
Each one names its open question in §8.

**FD-1. No new Lake dependency for Tier A; Physlib for Tier B's quantum information
(OQ-1).** Tier A builds on Mathlib at TCSlib's pin. Checked 2026-11-06 against Lean v4.25.0
and the pinned Mathlib: `Matrix.unitaryGroup`, `Matrix.PosSemidef`, `Matrix.kroneckerMap`,
`Matrix.trace`, `EuclideanSpace`, `Matrix.toEuclideanLin`, `GaussianInt` (in
`Mathlib.NumberTheory.Zsqrtd.GaussianInt`) and `GenContFract` all elaborate.

* **Why no dependency now.** Physlib's toolchain is v4.35.0, so depending on it means
  bumping all of TCSlib (and PFR). That is a maintainer decision, and Tier A should not wait
  for it.
* **Why no copying.** The import closure of Physlib's `Braket.lean` and `Qubit.lean` is 38
  modules and about 20,000 lines, written in the `module` / `public import` system of newer
  Lean. Copying it means backporting all of it, which costs more than the few hundred lines of
  overlap it would replace.
* **What we build instead.** Only what Tier A needs and Physlib lacks, plus the minimum
  overlap: kets, standard gates and the Born rule. The overlap copies Physlib's design (FD-2),
  so it can be deleted after the bump.
* **What we do not build.** Mixed states, POVMs, channels, fidelity, trace distance and
  entropy (`MState`, `POVM`, `CPTPMap`, `HermitianMat`). Every Tier B item that needs them
  (Q5.4, Q5.5, Q6.2 onward) is blocked on OQ-1, and that dependency is listed in each row.
  Rebuilding them here would duplicate a large, maintained library.

**FD-2. Registers and states follow Physlib's design.** A qubit is `Quantum.Qubit := Fin 2`,
as in Physlib. An `n`-qubit basis state is `Fin n → Qubit`. An amplitude vector is a function
`d → ℂ` on a finite type `d`, the carrier of Physlib's `Ket.vec`. A normalized state is the
structure `Quantum.Ket d` with Physlib's fields (`vec`, `normalized'`). Operators are
`Matrix d d ℂ`, and unitaries are `𝐔[d] := Matrix.unitaryGroup d ℂ`, with Physlib's
notation. Gates keep Physlib's names (`H`, `X`, `Z`, `S`, `CNOT`), but every `k`-qubit gate lives on `Reg k = Fin k → Qubit`, the shape `applyOn` needs, where Physlib uses `Qubit` and `Qubit × Qubit`; the bridge is a relabelling, stated when the dependency arrives. This
copies a design, not code, so §1c's *Design adaptation* citation applies. The classical side of
TCSlib uses `Bool` (languages, `BoolCircuit`, `BooleanAnalysis`), so `Quantum/Basic`
provides the bridge `Qubit ≃ Bool` and `basisOf : (Fin n → Bool) → (Fin n → Qubit)`. Class
definitions in Q4 read their inputs through it. *(This replaces the 2026-11-06 draft, which
used `Fin n → Bool`; see §11.)*

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
  Basic/Register.lean      Qubit, Ket (Physlib fields), basis kets, Qubit ≃ Bool, tensor of kets
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
TCSlib/Quantum/MixedStates.lean             (Tier B, blocked on OQ-1) consumer files only; MState,
                                            POVM, partial trace come from Physlib, not from here
TCSlib/Quantum/Algorithms.lean              (Tier B) QFT, PhaseEstimation, Shor/*, AbelianHSP
TCSlib/Complexity/Promise.lean              facade (namespace `Promise`); Promise/Basic.lean
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
| Q1.1 | `Qubit`, `Ket` (FD-2), basis kets, operators, tensors of kets, `Qubit ≃ Bool` | [dW26 §1.2–1.3, App. A]; design from [Physlib] | 1 / M | A |
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
| Q5.4 | Results that use mixed states, POVMs and the partial trace (these come from Physlib) | [dW26 §15.1] | 2 / M (**blocked on OQ-1**) | B |
| Q5.5 | Nayak's bound for quantum random access codes; then the 2-query LDC lower bound, linked to `KikuchiLDC` | [dW26 §15.2–15.3], [Nay99], [KdW04] | 5 / XL (**blocked on OQ-1**: von Neumann entropy from Physlib) | B |
| Q5.6 | Symmetric subspace: its dimension and the projector as an average over permutations | [Yue22 L4] | 3 / M | B |
| Q5.7 | Distributed Deutsch–Jozsa protocol (upper bound only); quantum fingerprinting using the codes in `ErrorCorrectingCodes` | [dW26 §16.3, §16.6] | 3 / M | B |

### Q6. QMA (`Complexity/Quantum/QMA`); Tier B

Q6.1 needs only Tier A objects (a witness register is extra wires). From Q6.2 on, the
acceptance operator, positive semidefinite operators and mixed witnesses lean on Physlib's
`HermitianMat` and `MState`, so those rows are **blocked on OQ-1**.

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
* **R5. Version drift and the Physlib switch.** A Mathlib bump in the middle of the campaign
  moves names, and switching to Physlib replaces the `Quantum/Basic` definitions.
  Mitigation: precise imports; FD-2's Physlib design keeps the switch mechanical; consumers
  read `Quantum/Basic` only through its lemmas (policy §1, no unfolding), so replacing the
  definitions only touches `Quantum/Basic`.
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
| OQ-1 | When does TCSlib bump Mathlib (and Lean and PFR) and take a dependency on Physlib `QuantumInfo`? Physlib is on Lean v4.35.0; TCSlib is on v4.25.0. | Tier A does not wait: it uses a thin layer with Physlib's design (FD-1, FD-2). Tier B's quantum-information items (Q5.4, Q5.5, Q6.2 onward) are blocked until the bump. On the bump, `Quantum/Basic`'s overlapping definitions are replaced by Physlib's. |
| OQ-2 | How are the course texts stored in `blueprint/src/references/`? | **Closed by the owner, 2026-11-06:** as for [AB09]. The PDF stays local; only the `sources.py` outputs (`<name>.raw.md`, `<name>.md`) and the `sources.json` entry are committed (§1a) |
| OQ-3 | Area and namespaces | **Closed by the owner, 2026-11-06:** `TCSlib/Quantum/` (namespace `Quantum`) for models and algorithms; `TCSlib/Complexity/Quantum/` (`QuantumComplexity`) for quantum classes; `TCSlib/Complexity/Counting/` (`Counting`) for PP and GapP; `TCSlib/Complexity/Promise/` (`Promise`) for promise problems (§4) |
| OQ-4 | Promise problems first-class from the start, or only from Q6? | Defined in Q0; BQP stated on languages, with a promise version |
| OQ-5 | Acceptance outcome `1` (de Wolf, Aaronson, AB09) or `0` (Watrous)? | `1`, with a deviation note wherever [Wat08] is cited |
| OQ-6 | Move `ErrorCorrectingCodes/QuantumHamming.lean` (already `Fin n → Fin 2`, with its own Pauli strings) onto `Quantum/Basic`? | Its register type already matches FD-2. Not in this campaign; queued in `backlog.md` as a later cleanup |
| OQ-7 | `ℝ`-valued quantum probabilities next to `ℚ`-valued `randProb`? | Keep both, with the Q0.9 cast lemma |
| OQ-8 | Official gate set: Watrous's {Toffoli, H, P}, {Toffoli, H} (real amplitudes), or gate-set-generic classes? | Watrous's set; gate-set independence waits for Solovay–Kitaev (Tier C) |
| OQ-9 | Mixed states and entropy: our own minimal layer or Physlib's? | Physlib's (FD-1). Closed by the owner, 2026-11-06, pending maintainer confirmation |
| OQ-10 | Where do campaign records live? | **Closed by the owner, 2026-11-06:** as for Arora–Barak chapters 3–4. Records live under `campaign/` on branch `quantum/campaign` (plan in `campaign/design/plans/`, gates in `campaign/gates/`, fills in `campaign/fills/`, backlog in `campaign/backlog.md`), kept off `main`; only Lean and its blueprint and reference files are merged to `main` |
| OQ-11 | Which elaboration check do agents run? `.claude/CLAUDE.md` says never to run `lean` or `lake build` and to use the VS Code infoview. `policy.md`'s review checklist (item 6) requires `zsh scripts/lean_check.sh <file>`, and `workflow.md` §6 uses `scripts/lean_check_tree.sh`. Cloud sessions have no infoview. | Follow `policy.md` and `workflow.md`: `lean_check.sh` per touched file, never `lake build` |

## 9. How this plan meets policy.md

No Lean has landed yet, so this section says how each rule is met when it does. The policy
review checklist is run on every PR of the campaign.

| `policy.md` rule | How the campaign meets it |
|---|---|
| §1 Layout, facades, `## Contents`, file size 150–600 lines | §4's tree; every topic has a facade; files split at about 600 lines |
| §1 Exports from `TCSlib.lean` | Each new facade (`Quantum`, `Complexity/Promise`, `Complexity/Counting`, `Complexity/Quantum`) is exported in the PR that creates it |
| §1 Precise imports, no bare `import Mathlib` | Every file imports exact modules (FD-1 lists the ones already checked) |
| §1 Area-local namespaces; root only for registered models | `Quantum`, `Counting`, `QuantumComplexity` (OQ-3); `QCircuit` at the root and registered (FD-12) |
| §1 Definitions separate from heavy theorems | `Basic/*` and the class-definition files carry definitions; theorems live in separate files |
| §1 *Definitions land with their lemmas* | Every public `def` ships with its `_eq`, `_iff`, case or `simps` lemmas in the same PR; no `@[simp]` without a gate; consumers never unfold another file's definition. Checked by `style_lint.py` check 8 |
| §1 *Hosts come first* | §6: HQ-1 is harvested into a public host before PP ⊆ PSPACE is briefed; no private search or recursion loops |
| §1 *Construction reuse* | Reuses `CVAL_mem_P`, `exists_isPUniform_of_mem_P`, `majority_error_le`, `NP_subset_PSPACE`'s enumerator, the `PolyTimeComputable` closure algebra |
| §1 *Duplication* must be human-approved | The Tier A overlap with Physlib (FD-1) is not in-repo duplication, but it is recorded and approved anyway (§11). Any copy of TCSlib material inside a fill is disclosed in its report |
| §1 File header | Copyright block, imports, the three standard `set_option`s, then a module docstring with `# Title`, `## Main definitions`, `## Main results`, `## References` |
| §2 `## References` and `[Tag, location]` on every declaration | §1's tags; locations are theorem, section or lecture numbers. Deviations (FD-4's gate set, FD-5's acceptance convention, FD-6's indexing) are stated in docstrings |
| §2 *Statement prose* | Every public declaration's docstring opens with a natural-language statement |
| §2 *Blueprint* and reference ingestion | §10 step 2: texts ingested under `blueprint/src/references/` with `scripts/sources.py` before the files citing them land; `\statementsource` only after an approved proofmatch run |
| §2 *Design adaptation* | §1c: Physlib cited in every `Quantum/Basic` module |
| §3 Proof sketches | A sketch under every `sorry` from the skeleton stage on; named steps become `have`s or lemmas; sketches change in the same commit as the proof |
| Checklist 6–7 | `zsh scripts/lean_check.sh <file>` with zero errors (OQ-11); `blueprint_validate.py --strict` and `dataset_hygiene.py --strict` when the blueprint is touched |

## 10. Getting started: the first three PRs

1. **This plan.** The owner raises it with the maintainers directly (no PR; the plan stays
   on `quantum/campaign`). OQ-1 is the question that needs them; OQ-2, OQ-3 and OQ-10 are
   closed.
2. **References.** Ingest [Wat08] and [dW26] (then [Aar10] and the rest as their phases
   start) by the §1a procedure: `python3 scripts/sources.py add Wat08=<local pdf>` and the
   same for `dW26`. The `add` step runs paid `claude -p` matching stages;
   `python3 scripts/dataset_pipeline.py --estimate` shows the cost first. The outputs land in
   the same PR as the first Lean file citing the tag.
3. **Phase P1 skeleton.** `Complexity/Promise`, `Complexity/Counting/{PP,GapP,Inclusions}`
   and `Quantum/Basic/*`, as statements with a proof sketch under every `sorry`, plus the
   FD-3 sanity theorems. Verify with `zsh scripts/lean_check.sh <file>` on each file,
   `python3 scripts/style_lint.py` and the policy review checklist, then write the
   `quantum-phase1` audit pack (`workflow.md` §3).

## 11. Decision log

Append-only. A superseded row is marked **Superseded** in place, never deleted.

| Date | Decision / event | By |
|---|---|---|
| 2026-11-06 | Plan drafted from [Wat08], [dW26] v6, [Aar10], [Gha20] and [Yue22]. Tiers A/B/C set (§2). | a-gupte (with Claude) |
| 2026-11-06 | **Superseded in part** (Physlib's design is now adopted; see the FD-1/FD-2 revision row below). External libraries consulted for comparison only, nothing taken: Physlib `QuantumInfo` (Lean v4.35.0, Apache-2.0); Timeroot/Lean-QuantumInfo (archived into Physlib, MIT); LionSR/QICLean (v4.36.0-rc1, Apache-2.0, contains `sorry`s and axioms); inQWIRE/LeanQuantum (v4.30.0-rc2, MIT); duckki/quantum-computing-lean (v4.33.1). None has quantum complexity classes. | a-gupte (with Claude) |
| 2026-11-06 | FD-1 to FD-12 adopted provisionally; OQ-1 to OQ-10 opened. | a-gupte (with Claude) |
| 2026-11-06 | Mathlib APIs FD-1 relies on checked to elaborate at the pin (Lean v4.25.0). | a-gupte (with Claude) |
| 2026-11-06 | **FD-1 and FD-2 revised.** Physlib's pure-state basics measured: their import closure is 38 modules and about 20,000 lines in the newer Lean module system, so copying is ruled out. Tier A keeps a thin Mathlib layer but adopts Physlib's design (`Qubit := Fin 2`, `Ket` fields, `𝐔[d]`, gate names; Physlib commit cdfa609, Apache-2.0, cited per §1c). Registers change from `Fin n → Bool` to `Fin n → Qubit`, with a `Qubit ≃ Bool` bridge. Mixed states, POVMs, channels and entropy are not rebuilt: Q5.4, Q5.5 and Q6.2 onward are blocked on OQ-1. OQ-9 closed provisionally (Physlib); OQ-6 simplified; OQ-11 opened. The overlap with Physlib (kets, standard gates, Born rule) is approved as a deliberate, temporary duplication, to be deleted when the dependency arrives. | a-gupte (approved) |
| 2026-11-06 | OQ-2, OQ-3 and OQ-10 closed by the owner, following the repository's precedents: references stored as for [AB09] (no PDFs; `sources.py` outputs only); the folder and namespace layout of §4; campaign records under `campaign/` on branch `quantum/campaign`, off `main`, as for Arora–Barak chapters 3–4. The plan moved from the repository root to `campaign/design/plans/`. The open-question register stays in §8 until `campaign/backlog.md` is opened. | a-gupte (decided) |
| 2026-11-06 | Phase P1 skeleton for Q1 (`TCSlib/Quantum/Basic/`: `Register`, `Gates`, `ApplyOn`, `Measure`, `Protocols`, two facades, export from `TCSlib.lean`) on branch `quantum/p1-basic`. Every module passes `scripts/lean_check_tree.sh` in dependency order; 42 `sorry`s, each under a proof sketch; `style_lint.py` 0 findings, `campaign_style_lint.py` 0 FAIL / 0 WARN. Every sorried statement was also checked numerically against the definitions (a script mirroring them entry by entry; all hold). Proved without `sorry` in the skeleton, to be declared in the audit pack: equation lemmas by `rfl`, `Ket.sum_prob` (the `normalized'` field), `cnotMap_involutive` and `toffoliMap_involutive` (by `decide`), and term-mode well-formedness inside definitions (`Ket.prod`, `Ket.relabel`, `wire`). FD-2 refined: gates on `Reg k`, not Physlib's `Qubit` types. OQ-11 followed: checks by `lean_check_tree.sh`, never `lake build`. | a-gupte (with Claude) |
