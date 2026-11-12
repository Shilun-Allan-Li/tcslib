# External audit pack — quantum E1 epoch boundary, round 2 (re-audit after repairs)

Campaign: quantum computation and complexity, plan `campaign/design/plans/QuantumComplexityPlan.md`.
Fill epoch E1 proved the 52 sorried statements of `TCSlib/Quantum/Basic/`; round 1 of its
boundary audit (`pack.md`, `findings.md`) ran at commit `a97fceca`.

**Why there is a round 2.** Round 1 reported 0 blockers, 2 majors and 7 minors. Both majors were
duplicated proof material. The gate rule (`workflow.md` §3–4) closes an epoch gate only on a round
with zero blockers and zero majors, and a round with majors triggers repairs and a full re-audit.
The repairs and every disposition are in `resolutions.md` (attached).

**This round audits the whole E1 surface again, at the repaired commit.** It has four tasks:
1. **Verify each repair** against the round-1 finding it answers (`resolutions.md`,
   § Dispositions). Where the repair adopted your round-1 construction, check that it is the
   construction you proposed.
2. **Audit every new or changed declaration from scratch.** Since round 1: 2 new public lemmas,
   3 new private helpers, 2 private helpers removed, 11 bodies changed, no signature changed.
3. **Re-verify the freeze against the gate baseline** from the cumulative diff, not only from the
   drift log: since `13c8664b`, the only changed bodies of audited declarations must still be the
   52 former `sorry`s, plus documentation.
4. **Re-run the debt check** (audit template failure mode 5) on the repaired files: confirm both
   majors are gone, classify every remaining copy-screen pair, and look again for the same fact
   proved twice in different words.

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 formalization at a fill-epoch boundary. The
proofs are machine-checked — do not review tactic scripts for correctness. The failure modes you
are hunting are:

1. **Infidelity** — a new public definition or statement that does not mean what its docstring
   or cited source says.
2. **Trivialization** — a new statement satisfiable for degenerate reasons.
3. **Freeze violation** — any audited declaration whose statement changed, or any body change
   other than replacing a `sorry`. Verify with the attached diffs.
4. **Stale documentation** — a proof sketch, module docstring or `## Main results` entry that no
   longer matches the code, including sketches of proofs the repairs changed.
5. **Debt** — wholesale duplication of existing proved material. Report it at **major** with the
   proposed fix "human acknowledgment required". Verify the ledger in `resolutions.md`
   (§ Round-2 baseline, copy-screen row) cumulatively.

For **each of the 2 new public declarations**: restate it in your own words before reading its
docstring, compare against the docstring and any cited source, and argue in 2–5 sentences that it
is true as stated. For the six public declarations of round 1, you may cite your round-1
restatements; check only that their statements are unchanged and that the docstring edits of
finding 4 are accurate. Do not give a blanket approval: an empty findings table must come with
the restatements, the repair-by-repair verification, and the freeze check.

## Scope

| Item | Where |
|---|---|
| Lean commit under audit | `647511e33e2c8b2a8c567362b0f3c756da78d2c9` on branch `quantum/e1-fill` of `Shilun-Allan-Li/tcslib`; the records (this pack, resolutions, evidence) are committed on top of it and change no Lean file |
| Round-1 commit | `a97fceca7c0f7b360f91cb08d4db5a5b33bdb548` |
| Audited baseline (gate close) | `13c8664b44f2550a66a8fb2c94c73069614f072f` |
| Change since round 1 | `evidence-r1/tcslib-r1-repairs.diff` (371 lines): `Gates`, `ApplyOn`, `Measure`, `Protocols`; 94 insertions, 66 deletions. `Register.lean` unchanged |
| Change since the gate baseline | `evidence-r1/tcslib-e1-r2.diff` (1294 lines): the five files, 747 insertions, 109 deletions. No other TCSlib file changed |
| Files under audit | the five files of `TCSlib/Quantum/Basic/` at the commit under audit, attached in full |
| Prior round | `findings.md` (round 1, verbatim) and `resolutions.md` |
| Fill report | `campaign/fills/e1/REPORT.md`, corrected in place for findings 8–9, with an errata section |
| Evidence | `campaign/gates/02-quantum-e1/evidence-r1/logs/` and `scripts/`, all produced at the Lean commit under audit |
| Standards | `policy.md`, `workflow.md` §3–4 |
| Sources | [dW26] arXiv:1907.09415 v6 §1.4, §2.1.2, App. A.4; optional |
| Out of scope | tactic proofs; the 33 counting-layer `sorry`s (epochs E2, E3; E2 is on a separate branch and gets its own boundary audit); statements accepted by gate `quantum-phase1` |

## Repository-side attestations (MEASURED, `evidence-r1/`)

- **Sweep (`logs/sweep.log`).** A fresh `scripts/lean_check_tree.sh` sweep of all 14 P1 modules in
  dependency order, never `lake build`. All pass. The 7 `Quantum` modules have no `sorry` warning
  and no other line containing `warning` or `error` (that is what the sweep's two counters
  count). Total: 33 `sorry` warnings, all in `Complexity/Promise` and `Complexity/Counting`.
- **Axioms (`logs/axioms.log`, `scripts/Axioms.lean`).** A census of the 267 non-internal
  constants of the audited modules. Private declarations have internal names and are not listed;
  they are covered through the public constants that use them and by the sweep's `sorry` count.
  - All **174** `Quantum` constants depend only on `propext`, `Classical.choice` and `Quot.sound`
    (or on none).
  - By kind (`scripts/axiom_diff.py`): against the gate's census, 21 added (8 source theorems,
    11 generated equation lemmas, 2 `congr_simp` lemmas), 0 removed. Against round 1, 2 added
    (the two new theorems), 3 removed (`cnotMap.eq_1`, no longer generated once `Protocols.lean`
    stopped unfolding `cnotMap`; two matchers whose patterns moved into the private
    `extend_wire`). `logs/axiom_diff_gate_to_e1fill.log` reproduces round 1's breakdown (22
    added: 6, 12, 2, 2) as a check of the script.
- **Drift (`scripts/drift.py`, revised for finding 7).** Comments stripped and whitespace
  normalized; `example` and unnamed `instance` are command boundaries and are inventoried
  separately; signatures, full bodies, and the per-file order of carried-over declarations are
  compared.
  - **Against the gate (`logs/drift_vs_gate.log`):** 211 → 248 named declarations; **0 removed,
    0 signatures changed, 52 bodies changed** (the former `sorry`s), 37 added (8 public,
    29 private), 159 unchanged; order the same in every file; anonymous commands 1 → 1 (the
    `Decidable` instance in `ApplyOn.lean`).
  - **Against round 1 (`logs/drift_vs_e1.log`):** 245 → 248; 0 signatures changed; 2 removed
    (private `X_pow_mul_self`, `Z_pow_mul_self`); 5 added (public `hadamardMat_conjTranspose`,
    `hadamardMat_mul_self`; private `mat1_ext`, `extend_wire`, `pow_mul_self_of_mul_self`);
    11 bodies changed; 232 unchanged; order the same; `Measure.lean`'s `example` removed.
- **Style.** `logs/style_lint.log`: 0 findings over the 14 P1 files. `logs/campaign_style_lint.log`:
  0 FAIL, 0 WARN. No line exceeds 100 characters (MAINTAINER).
- **Copy screen (`logs/copy_screen.log`, `scripts/copy_screen.sh`).** The script first lists
  every `example` in the screened files, since the repository's screen does not open a
  declaration there (finding 7): none. Then 132 declarations, 22 pairs: 15 among the E1 files
  (21 in round 1) and 7 inside `QuantumHamming.lean` and `QuantumSingleton.lean` (unchanged).

## What changed since round 1

| Finding | Change | Declarations touched |
|---|---|---|
| 1 (major) | anonymous `example` deleted | `Measure.lean` |
| 2 (major) | new public `hadamardMat_conjTranspose`, `hadamardMat_mul_self`; unitarity and `H_mul_H` derived from them; the four-entry split shared through new private `mat1_ext` | `hadamardMat_mem_unitaryGroup`, `Gate.H_mul_H`, `gate1_ext` (bodies) |
| 3 | sketch of `applyOn_permMat_mulVec_apply` names `Finset.sum_eq_single`; Hadamard sketches rewritten | docstrings |
| 4 | `applyOn_mulVec_apply`, `applyOn_wire_mulVec_apply` described as coordinate formulas for arbitrary matrices; "input bit `a`", output bit `y i` | docstrings |
| 5 | step comments in three long proofs | `applyOn_mul_applyOn_of_disjoint`, `no_cloning_of_overlap`, `teleport_outcome_prob` (comments only) |
| 6 | cross-file `simp [flipAt]`, `[cnotMap]`, `[hadamardMat]` → `flipAt_eq`, `cnotMap_eq`, `hadamardMat_apply` | `applyOn_wire_X_mulVec_basis`, `applyOn_wires20_CNOT_mulVec_basis`, `cnot_extend_wires01`, `flipAt_const`, `teleportState_vec`, `superdenseState_vec_aux` (bodies) |
| answer 3 | private `extend_wire` (write `u : Reg 1` on wire `i` = `update y i (u 0)`); private `pow_mul_self_of_mul_self` replaces `X_pow_mul_self`, `Z_pow_mul_self` | `applyOn_wire_mulVec_apply`, `applyOn_wire_X_mulVec_basis`, `teleport_correct` (bodies) |
| 7–9 | evidence tooling and the fill report's counts; no Lean change | — |

### The new public declarations (2)

| Declaration | File | Statement (informal) |
|---|---|---|
| `hadamardMat_conjTranspose` | `Gates.lean` | `hadamardMatᴴ = hadamardMat` |
| `hadamardMat_mul_self` | `Gates.lean` | `hadamardMat * hadamardMat = 1` |

Both sit before `hadamardMat_mem_unitaryGroup`, which now rewrites `star H * H` with them, and
before `Gate.H`. Both are in the module's `## Main results`.

## Specific questions for this round

1. **Repairs.** For each of findings 1–9, is the disposition in `resolutions.md` a correct and
   complete answer? For major 2, is the repair the construction you proposed ("factor a
   matrix-level Hadamard square lemma before constructing `Gate.H`; prove self-adjointness
   separately; use the shared square calculation in both audited proofs")?
2. **Freeze.** From `evidence-r1/tcslib-e1-r2.diff`, is every change to an audited declaration
   since the gate baseline still either a `sorry` replaced by a proof or a docstring edit? Do the
   11 bodies changed since round 1 all belong to E1 additions or to the 52 filled statements?
3. **New declarations.** Are `hadamardMat_conjTranspose` and `hadamardMat_mul_self` true,
   accurately documented, correctly placed, and not hidden duplicates of Mathlib lemmas? Are the
   three new private helpers general facts that policy §1 would want public?
4. **Debt.** Do you agree with the classification of the 15 remaining E1 pairs in
   `resolutions.md` as tactic idiom across different statements? Is there duplication the screen
   cannot see? In particular, `Gates.lean`'s `H_mul_Z_mul_H` still computes products of Hadamard
   entries; is that a different fact from `H H = 1`, or a copy?
5. **Tooling.** Does the revised `drift.py` answer finding 7 (order, anonymous commands)? Is the
   boundary check in `copy_screen.sh` an adequate answer for the copy screen, given that the
   shared script is not edited? Does `axiom_diff.py`'s classification match `workflow.md` §4,
   *Counting public names*?
6. **Documentation.** Do the sketches of every proof the repairs changed still describe the
   code? Are the errata and in-place corrections in `campaign/fills/e1/REPORT.md` accurate?
7. **Anything else.** Any regression, or anything the attestations misstate.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement or a freeze
violation; **major** = fixable but materially misleading as is, **or** accumulated debt (failure
mode 5) that the gate may not close over without explicit human acknowledgment; **minor** = edge
case, stale documentation, or naming/attribution defect; **note** = observation, no change
required.

## Attachments (the bundle)

One uploadable Markdown file, built by `evidence-r1/make_bundle.sh`. It contains this pack
verbatim, then under `## ===== <path> =====` headers:
- `findings.md` (round 1) and `resolutions.md`;
- the fill report (corrected, with errata);
- `campaign/gates/01-quantum-phase1/resolutions.md`;
- `policy.md` and `workflow.md`;
- `evidence-r1/tcslib-r1-repairs.diff` and `evidence-r1/tcslib-e1-r2.diff`;
- the five `Quantum/Basic` files at the commit under audit;
- every log and script under `evidence-r1/`.

The bundle is not committed; its SHA-256 and section count go in `resolutions.md` when the round
closes.
