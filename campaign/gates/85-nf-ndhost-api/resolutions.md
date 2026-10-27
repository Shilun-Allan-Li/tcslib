# The controller-stopped writer and one guess-then-run host (PR #174, an API gate): resolutions

**Gate, round 1:** the API gate of PR #174 (`lean/nf-ndhost-api` at `1045624d`). Pack `pack.md`;
bundle SHA-256 `19830ec7067d9df4db4c8cf801c9867093e9908831ce2725aaf645e7d2da050a` (71 sections),
the records at `d51ac787`. **Findings** (`findings.md`, verbatim, SHA-256 `1ce2ab83…`; received
2026-10-27): **FAIL, 0 blockers, 1 major, 2 minors, 13 notes.** The proofs are not questioned: the
major is a publication obligation, the minors are a docstring and a pack sentence.

**The round-1 fix:** commit `4c0a5943` on #174 (`evidence/round1-fix/round1-fix.patch`), for
findings 1 and 2; the campaign's records merged in by `086c0ef0` (no Lean change).

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | major | The new public definitions `GuessRunPhase.CtlState`, `guessCtlRunPhases` and `guessCtlRunRed` lack the reading lemmas policy §1 requires, and a landing adds no name to check 8. | **True; fixed** in `4c0a5943`, by policy §1's second form, case lemmas that together cover every input, none `@[simp]`, each by `rfl` (two by `cases` then `rfl`): the six fibers `GuessRunPhase.ctlState_pre`, `_guess`, `_skip`, `_back`, `_run`, `_out`; the six phases `guessCtlRunPhases_pre`, `_guess`, `_skip`, `_back`, `_run`, `_out`; the redirects `guessCtlRunRed_pre` (every setup state), `_guess_done`, `_guess_run` (every running writer state), `_skip` and `_back` (every seek state), `_run` (every run state), `_out` (every verdict). Check 8's list for `NDHost` is again the base's three names (`GuessRunPhase.State`, `guessRunPhases`, `guessRunRed`; `evidence/round1-fix/lint-head-TuringMachine.txt` against `evidence/lint-base-TuringMachine.txt`). The freeze: 25 → 56 public, the 19 added lemmas and the round's 12, nothing removed, no signature changed (`evidence/round1-fix/freeze-NDHost.txt`). The base's three names keep their warning (they predate this PR; not in the finding's scope). |
| 2 | minor | `guessCtlRunTM`'s docstring says "one step right" without the writer's endpoint-blank hypothesis. | **True; fixed** in `4c0a5943`: the docstring now names the step right `Turing.skipTM` and the rewind `Turing.skipBackTM`, which take one step and return the head of tape `j` to the stream's start when the stream has a blank on each side, the run lemmas' hypotheses. |
| 3 | note | The audit target is authentic and reconstructible. | Agreed. |
| 4 | note | The controller contract has the correct word-dependent scope and framing. | Agreed. |
| 5 | note | The bounded contract keeps its universal shorter-word clause. | Agreed. |
| 6 | note | The state-family generalization preserves the bounded instance and its finiteness requirements. | Agreed; finding 1's fibers are its readings. |
| 7 | note | One host implementation, the old host exactly its bounded, trivial-controller instance. | Agreed. |
| 8 | note | The public freeze and the consumers' compatibility are supported. | Agreed. |
| 9 | note | The stream offset, timing, framing and immediate-stop case are correct. | Agreed. |
| 10 | note | Both liveness cases of `guessCtlRunTM_stop_of_halted` hold; no blank-tape assumption is needed. | Agreed. |
| 11 | note | Forward padding and backward extraction are sound; `hV` is substantive and feasible for the planned verifier. | Agreed. NF's brief will state the verifier's `hV` obligation: every stopped stream, well formed or not, reaches a live verdict (a malformed display rejects through a live `rej`). |
| 12 | minor | "Unchanged declarations stay outside every seal" is not literal: the unchanged private `wr_tape_append` is in the first sealed region. | **True; erratum** (pack, brief item 4): the first sealed region, the writer's helpers and contracts, also covers the unchanged private `wr_tape_append`; the unchanged public bounded lemmas are outside every seal. Round 2's seal (`evidence/round1-fix/NDHostSealed.*`, generator `mkseal_nf3.py`) has eight regions, the round's five and the three blocks of finding 1's lemmas: 0 diagnostics. |
| 13 | note | The generalization resolves the first round's duplicated implementation; the dispositions are justified. | Agreed. |
| 14 | note | The broader absence-of-copies search remains a repository-side attestation. | Agreed. |
| 15 | note | Elaboration, axiom and replay records correspond to the audited source. | Agreed. At `4c0a5943` the module with 20 axiom prints elaborates with no diagnostic: the 16 theorems of the host family on the standard three, the four sampled case lemmas on none (`evidence/round1-fix/NDHostAx.*`). |
| 16 | note | The remaining lint and documentation claims are supported, subject to findings 1–2. | Agreed; both fixed. |

**The replay, round 2:** `replay-lnfapi4.sh` (`evidence/round1-fix/`), the same 4 modules, chained
from `oleans-lhh`, pinning the head's blob `c01cd773`. **Passed** (user, 2026-10-27): 4 of 4 at
`086c0ef0`, 0 failed, static-equal (`replay-lnfapi4.log`, `replay-lnfapi4-static.txt`); snapshot
`oleans-lnfapi4`.

**Round 2** (`pack-r2.md`, at `086c0ef0`): bundle SHA-256
`67bedf22d76355ebe3c993889ab4ef8ee9aac369fc54ba8c2edfd017fef59dde` (29 sections), the records at `62c35d13`.
The screen at `4c0a5943` is identical to round 1's head (none new, none gone; the case lemmas are
below the screen's minimum body). **Dispatched (user, 2026-10-27).** **Findings** (`findings-r2.md`,
verbatim, SHA-256 `7104c6b8c3214b749d93e772b85d7e85c7609dbd9fc76fb1916d41ec903e78bd`; received
2026-10-27): **PASS, 0 blockers, 0 majors, 1 minor, 11 notes.** The gate closes.

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The seal generator's description still says unchanged declarations stay outside every seal; its first region holds the unchanged private `wr_tape_append`. | **True; fixed** in the records (the generator's docstring only): the unchanged public declarations stay outside every seal, and the one unchanged private helper `wr_tape_append` is inside the first region. Re-run on the audited blob `c01cd773`, the generator's output is byte-identical to `NDHostSealed.lean.txt` (8 regions, 17 definitions, 4 erased). No Lean text is affected. |
| 2 | note | Target, provenance and fix scope verified. | Agreed. |
| 3 | note | The twelve fiber and phase equations are exhaustive readings (policy §1). | Agreed; round 1's finding 1 is resolved. |
| 4 | note | The seven redirect equations cover every input. | Agreed. |
| 5 | note | The delimiter qualification resolves round 1's finding 2. | Agreed. |
| 6 | note | The freeze attestation and the fix's scope are supported. | Agreed. |
| 7 | note | The eight-region seal is reproducible; the erratum is correct. | Agreed; finding 1 fixes the generator's text. |
| 8 | note | The duplication account is adequate. | Agreed. |
| 9 | note | Elaboration and axiom records match the audited source. | Agreed. |
| 10 | note | The lint attestation is supported; check 8 is the base's list again. | Agreed. The one-line difference is the policy linter's count: `scripts/style_lint.py` splits on newlines, so the empty text after the final newline counts as a line. The finding is unchanged. |
| 11 | note | Boundary cases and the shared implementation are intact. | Agreed. |
| 12 | note | The round-2 replay is a separate merge condition; the bundle carries no result for it. | Agreed; the replay ran after the bundle was staged. **`replay-lnfapi4` passed** (user, 2026-10-27): 4 of 4 at `086c0ef0`, the audited head, 0 failed, static-equal (`evidence/round1-fix/replay-lnfapi4.log`, `replay-lnfapi4-static.txt`). |

**Merge state. #174: clear to merge** at `086c0ef0f99a696f76c0f213f27c85a71902157a` (2026-10-27):
the gate passed in round 2, `replay-lnfapi4` passed at that head, the base is the campaign branch,
and the campaign has had no Lean change since the merge-in (merge base `f587e483`, 0 `.lean` files
differ at `210695f1`).
