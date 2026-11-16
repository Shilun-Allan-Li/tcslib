# Pass–shelat Gate 37, round 2 — sc-compose

**Verdict: CLEAR. 0 blockers, 0 majors, 0 minors.** All three round-1 findings are closed. No new finding or undisclosed duplicate was found. The two qualified reader statements have the same elaborated types as in round 1, up to definitional equality.

| Item | Audited revision |
|---|---|
| [Draft PR #324](https://github.com/Shilun-Allan-Li/tcslib/pull/324) | `4bd2d80bfb58fab5243c66c9f1a697a30b533756` |
| Round-1 head / unchanged PR base | `a6eaebd78c48e7fdfd06263edb84b70bc00ec593` / `6ce4658db08a1dc2a03a149987197660db078011` |
| Exchange | `f4287c3c7804dbae3b21fe831222941c2fc08d22` |
| Campaign records | `4de7ff85bfb4eaa53b4531218fca44fdf7cd64e2` |

## Round-1 findings

Paths below are under `TCSlib/Cryptography/`.

| ID | Round-1 severity | File · declaration | Round-2 finding and evidence | Disposition |
|---|---|---|---|---|
| G37-01 | major | `SecureComputation/ComposeSecurity/Machines.lean:145` · `ComposeMachines.encodeMsgs_append` | The proof is now exactly `TCSlib.Cryptography.CommitmentLemmas.encodeMsgs_append a b`. Its header is byte-identical to round 1. The added import supplies the unchanged public lemma at `ZeroKnowledge/CommitmentLemmas.lean:233`; the docstring explicitly attributes it. | **CLOSED** |
| G37-02 | major | `SecureComputation/ComposeSecurity/Bounds.lean:54` · `ComposeBound.length_encodeMsgs_le` | The proof is now exactly `TCSlib.Cryptography.CommitmentLemmas.length_encodeMsgs_le l c h`. Its header is byte-identical. `Bounds` obtains the unchanged public lemma at `CommitmentLemmas.lean:241` through `Machines`; its docstring names that source. | **CLOSED** |
| G37-03 | minor | Twenty formerly truncated formula insertions in ten helper files | All twenty are complete. After whitespace normalization, every replacement equals its declaration's full conclusion, or its defining reader's conclusion for `GoodRuns`, `sampleA` and `sampleB`. This includes all eleven readers named in round 1. These repairs change docstrings only. | **CLOSED** |

The approved public-lemma import is acyclic: the import closure of `CommitmentLemmas` contains no unit module. Including each root module, `Machines` grows from 82 to 129 modules, the unit closure from 98 to 145, and `Runs` from 86 to 133. Each increase is the same 47 modules.

## What is new since round 1

There is exactly one additional commit, **LE-gate37**, whose sole parent is the round-1 head; no rebase occurred. The commit contains an SSH signature. This audit checked its presence, not the signer's trust identity. The patch changes ten helper files, with 88 insertions and 36 deletions:

- the import and two public-lemma proof replacements;
- four `ComposeSim.splitCoins` qualifications in three declarations;
- twenty completed formulas and two attribution additions, affecting 22 docstrings.

The other seven edited files are code-identical after removing doc comments. The owned `ComposeSecurity.lean`, including the three target proofs, is byte-identical to round 1. Declaration names and order are preserved. The round-1 mathematical proof assessment therefore stands.

## The `splitCoins` side effect

**The qualification is acceptable. `composeCoins_fst` and `composeCoins_snd` retain their elaborated types, and `composeCoins` retains its elaborated body.** This conclusion follows from source/name-resolution checks:

1. In the round-1 `Runs` closure, the only declaration named `splitCoins` is `TCSlib.Cryptography.SecureComputation.ComposeSim.splitCoins`. Thus the old bare references denote that constant.
2. The new import also supplies `TCSlib.Cryptography.splitCoins`. It accepts two natural numbers and splits one tape into two; the local operation instead accepts the coin-length equality and assembles a main tape with run tapes. The head explicitly selects the original local constant. Its definition and the coin-length equalities are unchanged.
3. Replacing the four code occurrences of `ComposeSim.splitCoins` by `splitCoins` makes the head's entire `Runs.lean` code byte-identical to round 1 after removing doc comments. The arguments, result types and proof terms are otherwise unchanged. The successful rebuilt `Runs` and its consumers corroborate elaboration.

The supplied census is an axiom census, **not** a printed-type comparison. I did not run a fresh kernel-type dump, and do not require one to close this gate. The source argument establishes the same types up to definitional equality; it does not assert byte equality of serialized elaborator output.

Accordingly, decls2 is correctly **not empty**: it reports exactly two textual statement changes against round 1, with 193 public statements unchanged. Against the PR base it remains **185 ADDED, 0 CHANGED, 0 REMOVED**. The eleven pre-existing owned-file headers remain unchanged.

The two unchanged docstrings' bare `splitCoins` is understandable shorthand for the locally documented assembly operation: their equality-proof argument excludes the other operation. I do not grade this as a misstatement. No renaming, alternative import or fresh `Runs` seal is required; the change adds no definition unfolding or proof step.

## Verification and duplication

These are independent source checks and verification of supplied execution evidence, **not a fresh Lean build**.

| Check | Result |
|---|---|
| Integrity and provenance | All 19 outer manifest entries verify. Inner manifests verify 24 verification files, 201 landing files and 1,248 integration files, with exact file sets plus their manifests. All 19 bundle sections match their pinned Git objects. All 145 closure sources match the head. The included round-1 pack matches its pinned exchange revision. |
| Documentation | All 20 complete formulas match their conclusions in argument order. No formula ending in `…` remains. The remaining ellipses are explanatory prose. Every unit line is at most 100 characters; the largest file has 637 lines. |
| Landing rebuild | All 21 module records have return code zero, zero errors, zero sorry warnings and zero warnings. All source hashes match the PR head and final combined tree; all raw log hashes verify. |
| Integration | The 715 build records represent 694 effective modules after the 21-module rebuild. All 694 have return code zero and zero errors, and all source and raw log hashes verify. The existing unrelated admissions in the combined tree are disclosed. |
| Final merged state | Reconstructed built tree `3fb05ea062395caf069c09643a8caf751d3ad6da`. All six merge orders of the three remaining pinned heads onto `c2f6adeb` produce tree `e0d63d61d61efa7ef7d51a22a542be5e403a4004`; its `TCSlib` and `audits` subtrees equal the built tree's. All 694 effective source hashes also match this final tree. Explicit pinned historical merge bases were used because the reused checkout is shallow. |
| Rule 10 | All eight refreshed `Machines`/`Bounds` seals pass. Reconstructed source bytes, executed-probe hashes, raw log hashes, requested-name counts, install/EOF records and `maxErrors=0` agree. Canonical coe controls pass: eight probes and eight sealed negatives. Strict controls have twelve successful sealed negatives and only the four disclosed `ctlCoeReader` positive-control failures. |
| Axioms | The supplied combined probe gives only `propext`, `Classical.choice`, `Quot.sound` for the three targets and `polyTime_compose`. No new admission is introduced. |

I inspected every executable change since round 1: there is no new declaration or newly written proof beyond the approved public-lemma applications and name qualifications. Independent scans of the 153 new theorem signatures against the 43 tip-changed files, #326's 15 files and #327's 41 files find no match, including after normalizing binder names. The whole-head scan covers 20,722 theorems in 1,279 other files: its eight exact matches are DL-49 items; the additional binder-renamed match is the repaired G37-01 wrapper. G37-02's public counterpart was checked directly. These scans support the source review; they are not a completeness claim for semantic duplicate detection. No further undisclosed copy was found, and DL-49 is not reopened.

The merge order—#324 after #326 and #327—and any rebuild required when the other PRs merge remain maintainer merge conditions, not audit findings. No PR, branch, dispatch record or audited source was modified.
