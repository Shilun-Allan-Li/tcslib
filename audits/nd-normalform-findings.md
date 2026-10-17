Verified `nd-normalform-bundle.md` against SHA-256:

`da4bb710a6ef1f9d12677523212dcc7f1f3af7af0cd6fc95ca7fd994020ef723`

The relocation passes, with three minor documentation/evidence issues. I independently reconstructed the base files, compared declarations, checked blob hashes, and ran the supplied linter on the three attached Lean files. Lean is unavailable here; elaboration and replay results remain repository-side attestations.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | note | `NDNormalForm.lean` · `Turing.FinNDTM.exists_codeNDTM_accepts_linear` | **Q1: The move is exact and preserves the statement.** | Reversing the patch reproduces base blob prefixes `ad262c14` and `cecb4d9a`. All three head files match the replay’s full blob pins. The moved declaration and docstring are byte-identical. Namespace and all three options match; there are no inherited local variables or local notation. Both locations directly import `NTIME` and `NDCodes`. The other five declarations retain their statements, proof bodies, and order. | None. |
| 2 | note | `NTimeHierarchy.lean` · import and hierarchy sketch | **Q2: Existing consumers retain access.** | The fully qualified theorem name is unchanged, and the old module now directly imports its new home. The hierarchy sketch still cites that name. The supplied replay records four successful modules and six admissions, matching the source redistribution from six to five plus one. No consumer break is exposed by the supplied source. | None. Repository-wide consumer enumeration and build freshness remain attestations. |
| 3 | note | `ClassNP/NDNormalForm.lean` · module placement | **Q3: The new home is appropriate.** | The theorem combines the bundled machine/code layer with acceptance from `ClassNP/NTIME`; it does not depend on hierarchy-specific declarations. Placing it beside `ExhaustiveReplay` separates a reusable normalization result from its diagonalization consumer. | None. |
| 4 | note | C1 fill plan · question 3 | **Q4: Moving rather than copying is acceptable.** | The move preserves the public name and access through the former module while enabling separate file ownership. It creates neither a duplicate statement nor another admission. The deviation from the proposed alias arrangement is explicitly disclosed. | None. |
| 5 | minor | `ClassNP.lean` · `## Contents` | The facade fully documents its new child. | The import is present, but the Contents list omits `NDNormalForm`. Policy §1 requires one entry per child. The supplied linter checks import coverage, so its clean result does not establish Contents coverage. | Add a Contents entry describing the linear-overhead coded normal form. |
| 6 | minor | `move.py.txt`; `NOTES.md`; audit pack | **Q5: The saved move script accurately represents the final change and its checks.** | Script lines 88–91 rewrite an `NDCodes` docstring, whereas NOTES says that pointer remains unchanged and the final patch touches only three files. Also, the script reuses the extracted text but contains no before/after byte-equality assertion, contrary to NOTES and the pack. Independent comparison confirms equality nevertheless. | Record the omitted/reverted fourth-file edit or supply the final three-file script. Add an explicit equality assertion, or correct the description of the check. |
| 7 | minor | Audit pack · question 5 and evidence inventory | The PR body can be checked against the evidence. | No PR-body snapshot is included among the 27 sections. The patch contains a commit message, which does not establish the PR body’s contents. The supplied freeze, lint summaries, replay totals, and source counts otherwise agree. | Attach the PR body as reviewed at the audited head and compare its claims. |

The bundle also omits the imported `NTIME`/`NDCodes` definitions and the complete downstream source graph. Thus I verified unchanged import identities and local elaboration context, rather than independently inspecting those definitions or comparing kernel-elaborated types.

No new definitions are introduced. The moved theorem asserts that each bundled binary nondeterministic machine has one coded machine and one constant, fixed independently of input and budget: acceptance transfers forward within the stated linear allowance, while coded acceptance transfers backward at some unbounded time. It asserts no all-branch termination for the coded machine.

At sketch level, guessing a finite computation display and verifying its control, input reads, and work-tape histories supports both implications. For a fixed source machine, record width and the number of verification sweeps are fixed, giving the claimed linear allowance. This supports the unchanged statement; it does not discharge its remaining `sorry`.

Adversarial checks:

- **Empty input and zero budget:** the allowance remains `C`, preserving setup time.
- **A source that never accepts:** the backward implication prevents spurious coded acceptance despite the forward implication being vacuous.
- **Zero work tapes:** the retained input-verification sweep explains the `k+1` cost.
- **Infinite nonaccepting branches:** permitted; neither implication incorrectly requires their termination.

**PASS — 0 blockers, 0 majors, 3 minors, 4 notes.**
