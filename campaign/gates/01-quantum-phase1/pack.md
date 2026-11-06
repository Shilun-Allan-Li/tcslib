# External audit pack — quantum-phase1: the quantum basics and the counting classes (statement gate)

Campaign: quantum computation and complexity, plan `campaign/design/plans/QuantumComplexityPlan.md`
(branch `quantum/campaign`), statement phase **P1**. P1 contains plan items:
- **Q1**, quantum foundations;
- **Q0.1–Q0.6 and Q0.9**, promise problems, `PP`, gap functions;
- **Q0.7's statements**, the polynomial-time closure facts.

This is the campaign's first gate. Every later phase builds on these definitions, so a wrong
statement here is a **blocker**.

**This gate audits statements, not proofs.** The skeleton is definitions plus theorem statements,
with a proof sketch under every `sorry`. A few proofs already exist; they are declared below
(§ "Proofs present in the skeleton") and are part of the audited surface.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization: definitions, theorem
statements, and remaining `sorry`s. The proofs that exist are machine-checked — do not
review tactic scripts for correctness. The failure modes you are hunting are:

1. **Infidelity** — a definition that does not mean what the cited source means.
2. **Trivialization** — a definition or statement satisfiable for degenerate reasons
   (vacuous hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Unprovability** — a `sorry`d statement that is false as stated, or whose stated
   form is subtly weaker/stronger than intended (boundary cases: empty input, `n = 0`
   qubits, `k = 0` gate wires, random strings of length `0`).
4. **Missing hypotheses** — especially finiteness, positivity, and well-formedness side
   conditions the informal source leaves implicit.
5. **Debt** — wholesale duplication of existing proved material (private copies of
   another file's declarations, re-derivations of registry routines), even when
   disclosed and mechanically forced by file ownership. Report it at **major** with
   the proposed fix "human acknowledgment required": it does not block the gate on
   soundness, but the gate must not close without the human maintainer explicitly
   accepting the debt and naming its scheduled resolution. Screen for it
   cumulatively — verify the pack's duplication ledger (below) rather than assessing
   each item in isolation.

For **every definition** in scope: restate it in your own mathematical English *without
looking at the docstring first*, then compare your restatement against the cited source
location, and report any daylight. For **every `sorry`d theorem**: argue in 2-5 sentences
why it is true as literally stated, or exhibit the problem (ideally a concrete
counterexample or degenerate instance). Attempt at least **5** *adversarial
instantiations* — concrete pathological objects plugged into the definitions to check
they behave as the theory intends (§ "Suggested adversarial instantiations" lists
candidates; you are not limited to them). Propose any machine-checkable sanity theorems you
believe are missing.

Do not give a blanket approval. Your deliverable is the findings table; an empty table
must be accompanied by the per-definition restatements that justify it.

## Scope

| Item | Where |
|---|---|
| Commit under audit | `d2d72d18ed5b5845ff25ae028490ee45600ae38f` on branch `quantum/p1-basic` of `Shilun-Allan-Li/tcslib` |
| Lean files under audit (all lines) | the 14 files of the table below |
| Source texts | [Wat08] J. Watrous, *Quantum Computational Complexity*, arXiv:0804.3401 v1 (2008): §II.1 (promise problems; P, BPP, PP), §III.2 (gate set, Fig. 4), §IV.5 (GapP, PP). [dW26] R. de Wolf, *Quantum Computing: Lecture Notes*, arXiv:1907.09415 v6: §1.2–1.5, §2.1.2, App. A. Both freely available; **attach both PDFs** to the audit chat. Also cited, for standard facts only: [NC10] Nielsen–Chuang (10th anniv. ed.) §2.3, §4.5, Box 12.1; [FR99] Fortnow–Rogers, JCSS 59(2), §2; [WZ82] Wootters–Zurek, Nature 299; [AB09] Arora–Barak, ch. 17 and Def 7.3 |
| Plan and standards | `campaign/design/plans/QuantumComplexityPlan.md` (FD-1 to FD-12, §5 items Q0 and Q1); `policy.md`; `workflow.md` §2–3 |
| Received definitions the new files build on (not under audit, but read them) | `TCSlib/Complexity/Randomized/Classes.lean` (`randProb`, `polyLen`, `VerifierModel`, `boolVerifier`, `InBPP`, the `ClosedUnder…` pattern and its **Deviations** section); `TCSlib/Complexity/Randomized/PolyTimeModel.lean` (`polyTimeModel`); `TCSlib/Complexity/ClassNP/NP.lean` (`Complexity.NP`); `TCSlib/Complexity/ClassP/P.lean` (`Complexity.P`) |
| Out of scope | tactic proofs; the received files above; plan items not in P1 (circuits, BQP, query algorithms, QMA) |

### Files under audit (MEASURED, `evidence/logs/campaign_style_lint.log`, `evidence/logs/sweep.log`)

| File | Lines | Public decls | `sorry` warnings | Content |
|---|---|---|---|---|
| `TCSlib/Quantum/Basic/Register.lean` | 231 | 24 | 8 | `Qubit := Fin 2`, `Reg n := Fin n → Qubit`, `qubitEquivBool`, `basisOf`, `regAppendEquiv`; norm identities; `Ket` (Physlib's fields), `Ket.basis`, `relabel`, `prod` (`⊗ᵠ`), `evolve` |
| `TCSlib/Quantum/Basic/Gates.lean` | 308 | 45 | 12 | `permMat`, `Gate k := 𝐔[Reg k]`, `Gate.ofPerm`, `Gate.ofPhase`; bit maps `flipAt`, `cnotMap`, `toffoliMap`; `hadamardMat`, `zPhase`, `sPhase`; gates `H X Z S CNOT Toffoli`; gate identities |
| `TCSlib/Quantum/Basic/ApplyOn.lean` | 194 | 17 | 9 | `AgreeOff`, `applyOn` (plan FD-3), `applyOnU`, `wire`; algebra, commutation, Kronecker bridge, basis action, the `X`-on-a-wire sanity check |
| `TCSlib/Quantum/Basic/Measure.lean` | 120 | 11 | 6 | `Ket.prob` (Born rule), `Ket.probQubit`; normalization, basis states, invariance under gates on other wires |
| `TCSlib/Quantum/Basic/Protocols.lean` | 208 | 22 | 7 | `no_cloning`; `bell`; teleportation (`teleportInit`, `teleportState`, `bobVec`, three theorems); superdense coding |
| `TCSlib/Quantum/Basic.lean`, `TCSlib/Quantum.lean` | 31, 24 | 0 | 0 | facades |
| `TCSlib/Complexity/Promise/Basic.lean` | 146 | 13 | 3 | `Promise.Problem`, `ofLanguage`, `IsTotal`, `InPromiseP`, `InPromiseBPP` |
| `TCSlib/Complexity/Promise.lean` | 23 | 0 | 0 | facade |
| `TCSlib/Complexity/Counting/PP.lean` | 111 | 6 | 2 | `InPP E`, `InPromisePP E`; `randProb_cast_eq_sum` |
| `TCSlib/Complexity/Counting/GapP.lean` | 363 | 41 | 13 | `gap`, `IsGapP`, verifier combinators, six closure hypotheses, GapP closure, `inPP_iff_exists_isGapP` |
| `TCSlib/Complexity/Counting/PolyTime.lean` | 141 | 10 | 8 | the six closure hypotheses hold for `polyTimeModel`; `certVerifier` |
| `TCSlib/Complexity/Counting/Inclusions.lean` | 85 | 4 | 4 | `BPP ⊆ PP`, `PP` closed under complement, `NP ⊆ PP` |
| `TCSlib/Complexity/Counting.lean` | 32 | 0 | 0 | facade |

`TCSlib.lean` gains three imports (`TCSlib.Quantum`, `TCSlib.Complexity.Promise`,
`TCSlib.Complexity.Counting`).

## Repository-side attestations

Each attestation is marked as **MEASURED** (a log under `evidence/logs/`, produced by a script
under `evidence/scripts/`) or **MAINTAINER** (a claim of the author's, to verify or
challenge).

- **Toolchain (MEASURED).** Lean `v4.25.0`. Mathlib is at the pin in `lake-manifest.json`, with
  its cache fetched by `lake exe cache get`.
- **Elaboration (MEASURED, `logs/sweep.log`, `scripts/sweep.sh`).** Every module was re-checked
  from scratch at the commit under audit with `scripts/lean_check_tree.sh` (a direct `lean`
  invocation per module, **never `lake build`**, plan OQ-11), in dependency order. All 14 pass:
  exit 0, no error, a fresh olean, no diagnostic other than `declaration uses 'sorry'`. The total
  is **72** `sorry` warnings.
- **Dependencies (MEASURED, maintainer's run).** The 82 received TCSlib modules in the import
  closure of `Randomized.Classes`, `Randomized.PolyTimeModel` and `ClassNP.NP` were checked the
  same way in dependency order: 82 pass, 0 fail. Their oleans are the ones the sweep imports.
- **Axiom census (MEASURED, `logs/axioms.log`, `scripts/Axioms.lean`).** It lists every
  non-internal constant declared in the audited modules with the axioms it depends on: 228
  constants. No axiom occurs other than `propext`, `Classical.choice`, `Quot.sound` and
  `sorryAx`. Of the constants:
  - 119 do not depend on `sorryAx`;
  - 90 theorems do. Of these, **72 contain a `sorry` of their own**, matching the sweep. The
    other **18** are `rfl` equation lemmas whose statements mention a definition with a sorried
    proof field (next item): `Gate.{H,X,Z,S,CNOT,Toffoli,ofPerm,ofPhase}_coe`, `applyOnU_coe`,
    `Ket.{basis,relabel,prod,evolve}_vec`, `bell_vec`, `bobVec_apply`, `denseCode_eq`,
    `teleportState_eq`, `superdenseState_eq`;
  - 19 definitions do (next item).
- **Definitions that inherit `sorryAx` (MEASURED, `logs/axioms.log`).** 19 definitions carry
  `sorryAx` **only through a `Prop`-valued field** (a normalization or unitarity proof) that cites
  a sorried lemma. Their data (amplitude vectors, matrices) is given explicitly and does not
  depend on `sorry` (MAINTAINER; please verify). They are:
  - `Ket.basis`, `Ket.relabel`, `Ket.prod`, `Ket.evolve`, `bell`;
  - `Gate.ofPerm`, `Gate.ofPhase`, `Gate.H`, `Gate.X`, `Gate.Z`, `Gate.S`, `Gate.CNOT`,
    `Gate.Toffoli`;
  - `applyOnU`, `teleportInit`, `teleportState`, `bobVec`, `denseCode`, `superdenseState`.

  **Question 1 below asks whether this is acceptable.**
- **Style (MEASURED, `logs/style_lint.log`, `logs/campaign_style_lint.log`).** `scripts/style_lint.py`
  reports 0 findings over the 14 files. `scripts/campaign_style_lint.py` reports 0 FAIL and
  0 WARN; it checks statement-prose docstrings, a sketch before every `sorry`, file sizes,
  `## References`, facade coverage, and public definitions with no lemma beside them (check 8).
- **Collision screen (MEASURED, `logs/collision.log`, `scripts/collision.sh`).** The tree has 936
  Lean files. No file outside the audited ones opens a `Quantum`, `Counting`, `Promise` or
  `QuantumComplexity` namespace or declares a name in them. A positive control confirms the
  screen finds them in the 10 audited files that do.
- **Numerical statement checks (MEASURED, `logs/numeric.log`, `scripts/numeric_*.py`).** The two
  Python scripts mirror the Lean definitions entry by entry: gates as matrices indexed like the
  Lean `(y, x)`, `applyOn` by the same entrywise rule, verifiers as functions on bit lists. They
  check the sorried statements on small instances and random unitaries: 27 checks, 0 failures.
  - **Quantum:** `H_mul_H`, `S_mul_S`, `H_mul_Z_mul_H`, `X_eq_H_mul_S_mul_S_mul_H`,
    `Toffoli_apply_of_control_one`, `applyOn_mul`, `applyOn_conjTranspose`, `applyOn_one`,
    `applyOn_commute_of_disjoint`, the Kronecker bridge, `applyOn_wire_X_mulVec_basis`,
    `teleportState_vec`, `teleport_outcome_prob`, `teleport_correct`, `superdense_decode`.
  - **Counting:** every `gap_*` lemma, `gap_boolVerifier`, `randProb_coinFill`, and the
    schedule arithmetic the sketches of `IsGapP.add`, `IsGapP.mul`, `inPP_iff_exists_isGapP` and
    `InPP.compl` use.

  This is evidence, not proof. It cannot see `Fin`-cast or coercion subtleties the Lean
  statement might add.
- **Hosts (MAINTAINER).** P1 introduces no search, recursion, interpreter, runner or input
  device (policy §1, *Hosts come first*; review checklist item 8). It builds no machine.

## Proofs present in the skeleton (part of the audited surface)

`workflow.md` §2 allows proofs in a skeleton only for definitional unfolding. These exist
(MEASURED in `logs/axioms.log`, where they appear as `CLEAN` theorems):

- **Equation and characterization lemmas by `rfl` or `Iff.rfl`.** These are the `_eq`, `_apply`,
  `_coe`, `_vec` and `_iff` lemmas of the new definitions, as policy §1 (*Definitions land with
  their lemmas*) requires.
- **`Quantum.cnotMap_involutive` and `Quantum.toffoliMap_involutive`**, by `decide` over the 4
  and 8 basis states.
- **`Quantum.Ket.sum_prob`**, which is the structure field `normalized'` restated.
- **Well-formedness proofs inside definitions:**
  - `Ket.relabel` and `Ket.prod` combine sorried norm lemmas with the input kets'
    normalization (`Eq.trans`, `rw`);
  - `wire i` proves injectivity of a map out of `Fin 1` (`Subsingleton.elim`);
  - `wires01` is `Fin.castLEEmb (by decide)`;
  - `Promise.ofLanguage` proves disjointness of `L` and its complement;
  - `AgreeOff`'s `Decidable` instance is `inferInstanceAs`.

Lean also generated some structure lemmas itself (`Ket.ext`, `Ket.ext_iff`, `mk.inj`,
`mk.injEq`, `mk.sizeOf_spec`, for `Ket` and `Promise.Problem`).

## Known deviations (declared by the authors — verify they are benign, flag any others)

- **Kets (`Register.lean`).** They are read through the field `Ket.vec`. [Physlib] also makes
  `Ket d` a `FunLike`; that is omitted so the definitions can later be replaced by Physlib's
  (plan FD-2).
- **Gate carriers (`Gates.lean`).** Every `k`-qubit gate lives on `Reg k = Fin k → Qubit`, where
  [Physlib] uses `Qubit` and `Qubit × Qubit`. The names are Physlib's.
- **Wire conventions (`Gates.lean`).** `CNOT` has control `0` and target `1`. `Toffoli` has
  controls `0, 1` and target `2`. `Gate.S` is Watrous's phase gate `P` [Wat08, §III.2].
- **`applyOn` (`ApplyOn.lean`).** It is defined entrywise through an embedding of wires, not as a
  reordered Kronecker product (plan FD-3); the Kronecker form is a theorem
  (`applyOn_castAdd_eq_reindex_kronecker`).
- **No-cloning (`Protocols.lean`).** The proof route is the linearity argument of [WZ82], not the
  inner-product argument of [NC10, Box 12.1]; the statement is the same. One-qubit states are
  kets over `Reg 1`.
- **Promise `P` (`Promise/Basic.lean`).** It is stated as "some language in `P` separates the
  yes-instances from the no-instances", not by a machine [Wat08, §II.1].
- **Promise `BPP` (`Promise/Basic.lean`).** It is stated with "rejects with probability ≥ 2/3"
  on no-instances, as in `InBPP`; [Wat08] says "accepts with probability ≤ 1/3".
- **Abstract machines (`PP.lean`, `GapP.lean`).** As for the received `Randomized.InBPP`,
  machines are replaced by an abstract `VerifierModel` with random strings of length
  `polyLen a k |x|`. The intended instance is `Randomized.polyTimeModel`.
- **Abstention (`GapP.lean`).** Gap functions use verifiers valued in `Option Bool`, where
  `none` abstains. [Wat08, §IV.5] and [FR99] use nondeterministic machines with
  `#accept - #reject` instead. The reason, recorded in the plan's decision log: with
  fixed-length random strings and no abstention, every gap at length `m ≥ 1` is even, and
  padding multiplies gaps by powers of `2`, so GapP would not be closed under exact sums.
- **Closure hypotheses (`GapP.lean`).** The closure properties are named hypotheses on `E`.
  Their `polyTimeModel` instances are separate, sorried statements in `PolyTime.lean`.
  Closure under polynomial-time *preprocessing* of the input is **not** included; it is
  deferred to the phase that needs it (plan Q0.3).
- **Citations to [AB09] for `PP` (`PP.lean`, `Inclusions.lean`)** are at chapter level
  (`[AB09, ch. 17]`). The exact item will be fixed when the text is ingested (plan §1a). The
  [Wat08] citations are exact.

## Duplication ledger

- **Copies of TCSlib proved material:** none. No file under audit copies a declaration of
  another TCSlib file (MAINTAINER; the files are new, and none is `private`).
- **Overlapping definitions inside TCSlib (disclosed, no proved material).** The root-level
  `sigmaX` and `sigmaZ` of `TCSlib/ErrorCorrectingCodes/QuantumHamming.lean` are matrices on
  `Fin 2` that mean the same as `Gate.X` and `Gate.Z` here, which live on `Reg 1`. No lemma is
  duplicated. Merging them is plan OQ-6, queued as a later cleanup.
- **Overlap with an external library (approved).** Kets and the standard gates overlap with
  Physlib `QuantumInfo` (design adapted, no code transcribed). The plan's decision log records
  this as approved by the owner as a temporary duplication, to be deleted when the Physlib
  dependency arrives (plan FD-1, OQ-1).

## Specific questions for this phase

Ordered by how much later work depends on the answer.

1. **Definitions that inherit `sorryAx`.** Nineteen data definitions (`Gate.X`, `Ket.basis`,
   `Ket.evolve`, …) take their unitarity or normalization field from a sorried lemma. Until that
   lemma is filled, every theorem mentioning them prints `sorryAx`, even an `rfl` equation lemma.
   Is this acceptable for a skeleton? The alternative is proving these small lemmas now:
   permutation matrices and the Hadamard matrix are unitary, unit-norm diagonals are unitary,
   and a few sums of squared norms. Would you require it before the gate closes?
2. **`applyOn` (plan FD-3).** Every quantum circuit will be built from it.
   - Is the entrywise rule (`U (y ∘ w) (x ∘ w)` when `y`, `x` agree off the range of `w`, else
     `0`) exactly "`U` on wires `w`, identity elsewhere", with gate wire `j` mapped to register
     wire `w j`?
   - Is `applyOn_castAdd_eq_reindex_kronecker` oriented correctly: the gate on the *first* `k`
     wires, `regAppendEquiv k m (a, b)` reading `a` there?
   - Check the degenerate case `k = 0`: `applyOn` of a `1 × 1` matrix `u` is `u • 1`.
3. **Conventions in the gate matrices.**
   - `hadamardMat y x = (-1)^(x·y) / √2`.
   - `permMat σ y x = [y = σ x]`, so the matrix maps `|x⟩` to `|σ x⟩`.
   - `Ket.evolve U ψ = U *ᵥ ψ`.
   - In `teleportState_vec`, `X^{y₁} Z^{y₀}` is an element of the unitary group: `Z` is applied
     first.

   Are these consistent with each other and with [dW26, §1.4–1.5]?
4. **Teleportation and superdense coding statements.** Do `teleportState_vec`,
   `teleport_outcome_prob`, `teleport_correct` and `superdense_decode` say what [dW26, §1.5] and
   [NC10, §2.3] mean, with the wire assignment of `teleportInit`? `teleport_correct` states Bob's
   corrected *unnormalized* vector equals `½ ψ`. `superdense_decode` states only the measurement
   probability, so it is robust to a global sign. Are these the right strengths?
5. **No-cloning.** The statement forbids a unitary that copies *every* state *exactly*, with a
   fixed blank state. It does not cover cloning up to a global phase, or cloning two given
   non-orthogonal states. Is the statement as given the standard one, or should it be
   strengthened now, given that later phases do not use it?
6. **One-wire measurement.**
   - Is `probQubit` (the total probability of basis states with wire `i` equal to `b`) the Born
     rule for measuring one qubit [dW26, §1.2.2]?
   - Is the hypothesis `∀ j, w j ≠ i` of `probQubit_evolve_applyOnU_of_forall_ne` exactly "the
     gate avoids wire `i`"?
7. **Abstaining verifiers and GapP (the main design decision).**
   - For `polyTimeModel`, is `IsGapP polyTimeModel` the standard class GapP? The authors' claim:
     an abstaining path is a pair of an accepting and a rejecting nondeterministic branch, and
     conversely a nondeterministic machine's paths can be laid out on one length of random
     string, with padding paths abstaining. No equivalence theorem is stated. Should one be,
     as a sanity theorem?
   - Can abstention trivialize anything, for example a verifier that abstains everywhere,
     whose gap is identically `0`?
8. **Vacuity of the closure hypotheses.** The theorems of `GapP.lean` and `Inclusions.lean`
   assume up to five of the six hypotheses.
   - Is each hypothesis true for `polyTimeModel`, as `PolyTime.lean` states?
   - Check `ClosedUnderPad`: its schedule is `polyLen a k n + c`, and the verifier reads
     `r.take p` and requires the rest to be all `false`.
   - Check `ClosedUnderCoinFill`: its verifier reads one bit after position `p`.
   - Check `ClosedUnderGapProd`: the split point is a polynomial schedule.
   - Is any hypothesis stronger than needed, or impossible for a natural model?
9. **The `PP` definition.** `InPP E L` requires `x ∈ L ↔ 1/2 < Pr[M accepts x]`, with a Boolean
   verifier on the schedule `polyLen a k`. With `E = polyTimeModel`, is this exactly `PP`
   [Wat08, §II.1], [AB09, ch. 17]? In particular, is the restriction to schedules of the form
   `a (n+1)^k` harmless, and is `randProb`'s `ℚ` threshold `1/2` the intended strict inequality?
10. **`NP ⊆ PP`.** The statement is for `polyTimeModel` and uses `Complexity.NP`'s exact-length
    certificates `C (|x|+1)^c` (that is `polyLen C c`). Does the sketch (gap `2 · #cert - 1`) work
    at `x = []` and with `C = 0` (the empty certificate only)?
11. **Promise problems.**
    - Is `Promise.Problem` (two disjoint sets, no totality) [Wat08, §II.1]'s notion?
    - Is the separator formulation of promise `P` equivalent to Watrous's machine formulation?
    - Do `inPromiseP_ofLanguage_iff` and `inPromiseBPP_ofLanguage_iff` state the right
      reductions to the language classes?
12. **`randProb_cast_eq_sum` (plan FD-11).** Is "a sum over all `2^m` strings of indicator / `2^m`,
    in `ℝ`" the right form to meet quantum acceptance probabilities in the later `BPP ⊆ BQP`?
    (It is not used in P1.)
13. **Missing sanity theorems.** For example: `Gate.X ≠ 1`; `applyOn` on a register where the gate
    wires are not the first ones, beyond `applyOn_wire_X_mulVec_basis`; a nontrivial `PP`
    language; `gap` of a Boolean verifier against an explicit count.

## Suggested adversarial instantiations

- `n = 0`: `Reg 0` has exactly one element; `Ket (Reg 0)`; `applyOn` with `k = n = 0`.
- `k = 0` gate wires with `n ≥ 1`, through any `Fin 0 ↪ Fin n`.
- `m = 0` random bits in `gap`, `constVerifier`, `sumVerifier` at length `1`, and
  `prodVerifier` with `p = 0`.
- `padVerifier` and `coinFill` on random strings *shorter* than the schedule. The gap lemmas
  exclude these by hypotheses; check those hypotheses are enough.
- The verifier models `Eff ≡ True` (every language is in `InPP`) and `Eff ≡ False` (none is).
  Confirm no theorem's content hinges on either, and that each closure hypothesis holds in
  both.
- `L = ∅` and `L = univ` in `InPP`, `InPP.compl`, `inPP_iff_exists_isGapP`.
- A `Ket` over a one-element basis, and `no_cloning`'s `[Nontrivial d]` hypothesis.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = statement is fixable but materially misleading as is, **or** accumulated
debt (failure mode 5) that the gate may not close over without explicit human
acknowledgment; **minor** = edge case or naming/attribution defect; **note** =
observation, no change required.

## Attachments (the bundle)

The bundle is one uploadable Markdown file. It contains this pack verbatim, then each attachment
under a `## ===== <path> =====` header:
- `policy.md` and `workflow.md`;
- the plan;
- the 14 audited files, and the `TCSlib.lean` import list;
- the four received files named in § Scope;
- every file under `evidence/logs/` and `evidence/scripts/`.

The bundle is **not committed** (`workflow.md` §3). The resolutions file will record its
SHA-256 and section count. The two source PDFs ([Wat08], [dW26]) are attached to the audit
chat separately.
