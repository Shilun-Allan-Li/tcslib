# Chapter 2, epoch 2, batch C — continuation checkpoint

**Status: incomplete, 2 of 3 targets filled. Do not close batch C on this archive.**

`HALT_NPHard` and `HALT_not_mem_NP` are filled and kernel-checked. Their only
admitted dependency is exactly the brief-sanctioned `Complexity.NP_subset_EXP`.
The full 53-module sweep passes with zero errors. All 34 new private helpers
are admission-free.

`mem_NP_iff_exists_length_le` remains admitted at two explicit machine
obligations: polynomial-time membership of the forward paired verifier and
the reverse padded verifier. The witness equivalences, search uniqueness,
padding/stripping specifications, and required rejection behavior are proved.
These semantic results do **not** discharge the machine obligations. Its
`sorryAx` is an outstanding defect under the completion criterion, not a
sanctioned dependency. This archive uses the brief's continuation provision;
`CONTINUATION.md` identifies the exact remaining work.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Base branch: `complexity/arora-barak-ch1`
- Base commit: `6c09453e6af59ff1575060b66196d28812800d24`
- Working branch, created off that exact base as the brief requires: `fill/ch2-e2-C`
- Delivered commit: `3a7201b13789c5c2f051e69203257f03d3d494c1`
- Delivered tree: `3382c0564df63e9b94e20b88f0534967b1bee538`
- Binding brief: `briefs/ch2-epoch2-batchC.md` at the base commit.
- Lean: `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent, no delegation.

Only the two owned tracked files changed:

- `TCSlib/Complexity/ClassNP/NP.lean`
- `TCSlib/Complexity/ClassNP/Reductions.lean`

No other branch was checked out or changed. There was no push or PR. All
existing public declarations, statement signatures, hypotheses, docstrings,
AB09 attributions, imports, and option headers are preserved. There are no
removed declarations or new public declarations. All existing non-target
declarations and their proofs are untouched.

## Target disposition, in the assigned order

| Target | Status | Work and remaining obligation |
|---|---|---|
| `mem_NP_iff_exists_length_le` | **Open** | Follows the audited two-verifier construction. Both witness equivalences are proved. Two inline `sorry` terms remain, each proving a verifier language is in `P`; neither is hidden in a helper. |
| `HALT_NPHard` | Filled | Uses `NP_subset_EXP`, normalizes the total singleton-indicator decider with `one_work_tape_binary`, transforms its control, applies `exists_codeTM`, and uses fixed-code prefixing. Only `decode_encode` is used of the representation scheme. |
| `HALT_not_mem_NP` | Filled | Converts the assumed NP membership through `NP_subset_EXP` to a total decider, proves its singleton indicator equals `[HALT c s]` on every string, and contradicts `HALT_not_computable`. The `EffectiveMachineCode` hypothesis is unchanged. |

The first target was developed before moving to the HALT pair. It is not
being reported as false or as unprovable: the missing work is construction
and timed verification of its two machines. No mathematical obstruction to
the frozen statement was found.

### Exercise 2.1: audited edge cases

These are semantic discharges; the pending timed machines must implement
the same checks.

| Edge case | Where discharged |
|---|---|
| `C = 0` | `certificate_room` is quantified over all natural coefficients. The old witness bound forces the empty witness, and `paddedVerifier_witness` pads it with a marker using coefficient `C+1`. No positivity hypothesis on `C` is used. |
| `c = 0` | `certificateTotal_strictMono` derives strictness from the additive input length, not strict growth of the power. `certificate_room` uses only `(n+1)^c ≥ 1`. Both proofs include degree zero. |
| `x = []` | `paddedVerifier_append` proves the recovered split for every input, including length zero; `take`/`drop` at that boundary recover the entire certificate region. |
| `u = []` | `stripCertificate_pad` includes an empty old witness. The marker itself is retained in the padded region, and `paddedVerifier_witness` proves its exact length. |
| All-false region | `stripCertificate_false` and `paddedVerifier_no_marker` prove rejection, including when the input contains true bits. Stripping operates only on the suffix after the recovered boundary. |
| Malformed strings | `pairedVerifier_malformed` rejects failed grammar parsing; `paddedVerifier_no_split` rejects missing length solutions. `certificateSplit_zero` covers empty total input. `stripCertificate_spec` characterizes every successful strip as a last-true decomposition. |
| Marker after too many witness bits | `paddedVerifier_too_long` proves rejection even for a correctly marked word of the enlarged exact width. The original bound is explicitly present in `paddedVerifier`. |

### HALT control modification

The named control-modification lemma is **`acceptTM_halts_iff`**; its run
invariant is `acceptTM_run`, derived from `acceptCfg_step`.

The state space is `Option (M.State × Bool)`. A simulated source state carries
the remembered bit; the inner `none` is a live loop state, distinct from a
configuration's outer `none` halting state. `acceptAction` first updates the
register with the action's optional output, then redirects the successor
state. Consequently an emission on the halting transition is included.
`acceptTM_loop` proves the stationary live configuration stays fixed at every
time. The real output is suppressed, and the tape count is unchanged.

The separate emit-then-copy machine is `prefixTM`. Its proved budget is
`|w| + |x| + 1`; `fixedPair_computes` explicitly specializes this to
`2|α| + |x| + 3`. It does not substitute the diagonal-pairing machine.

## New declarations

All names below are private, in namespace `Complexity`; there are **34**.
The axiom log checks every one, including definitions and theorems.

### NP.lean: 18 private declarations

| Name | Statement or role |
|---|---|
| `stripCertificate` | Removes the last true marker and its false suffix, returning failure if no marker exists. |
| `stripCertificate_false` | All-false input strips to failure. |
| `stripCertificate_pad` | A word followed by a marker and false run strips back to that word. |
| `stripCertificate_spec` | Failure is equivalent to being all false; success is equivalent to a last-true decomposition. |
| `certificateTotal_strictMono` | Input length plus repaired exact width is strictly increasing. |
| `certificate_room` | The repaired exact width exceeds the original bound by at least one. |
| `certificateSplit` | Executable bounded search for a legal length split. |
| `certificateSplit_spec` | The search returns a given index exactly when that index solves the length equation. |
| `certificateSplit_zero` | Total length zero has no legal split. |
| `pairedVerifier` | Forward verifier language, using `pairDecode`, the exact length test, and the old verifier. |
| `pairedVerifier_pair` | Membership on genuine pairs has exactly the intended meaning. |
| `pairedVerifier_malformed` | Failed pair parsing implies rejection. |
| `paddedVerifier` | Reverse verifier language, with split search, marker stripping, original-bound check, and old paired verification. |
| `paddedVerifier_no_split` | Failed split search implies rejection. |
| `paddedVerifier_append` | A correctly sized certificate region is split at exactly the original input boundary. |
| `paddedVerifier_no_marker` | An all-false certificate region is rejected. |
| `paddedVerifier_too_long` | An overlong stripped witness is rejected, even inside a valid exact-width region. |
| `paddedVerifier_witness` | Exact padded witnesses and old bounded paired witnesses are equivalent. |

### Reductions.lean: 16 private declarations

| Name | Statement or role |
|---|---|
| `acceptState` | Maps a source state and captured bit to a simulated, halting, or live-loop state. |
| `acceptAction` | Copies the source tape actions, updates the bit before halt redirection, and suppresses output. |
| `acceptTM` | Finite control-transformed machine with unchanged tape count. |
| `acceptCfg` | Configuration correspondence using the source output's last bit. |
| `acceptTM_loop` | Every run from the live loop configuration remains at that configuration. |
| `acceptCfg_apply` | Action application commutes with the configuration correspondence. |
| `acceptCfg_step` | The correspondence commutes with every source step. |
| `acceptTM_run` | Initialized runs correspond at every time. |
| `acceptTM_halts_iff` | For a total singleton-bit source decider, transformed halting is equivalent to a true bit. |
| `prefixTM` | Zero-work-tape fixed-prefix emission followed by input copying. |
| `prefixCfg` | Configuration notation for the prefix machine. |
| `prefixTM_emit` | Fixed-prefix phase run invariant. |
| `prefixTM_copy` | Input-copy phase run invariant. |
| `prefixTM_computes` | Exact linear bound for fixed prefixing, including the final halting step. |
| `fixedPair_computes` | Audited `2|α| + |x| + 3` bound for fixed-code pairing. |
| `fixedPair_polyTime` | Polynomial-time computability of fixed-code pairing. |

## Requested shared lemmas

For serial promotion at a maintainer's discretion:

1. An existential public fixed-prefixing theorem from `prefixTM_computes`,
   in the composition layer, with the same `|w| + |x| + 1` bound.
2. Its fixed-code pairing specialization from `fixedPair_computes`, in the
   encoding layer. This is distinct from diagonal pairing.

The implementations remain private in the owned file. No shared file was
modified. The two verifier constructions remain this batch's continuation
obligations, not assumed shared results.

## Escalations and continuation

**Completion escalation:** Exercise 2.1 is unfinished. Its direct `sorryAx`
root violates the brief's clean-target requirement, so the gate remains open.
There is no proposed statement alteration. Continue from the delivered
commit using `CONTINUATION.md`, replacing both verifier-membership admissions
with actual timed machine proofs. Preserve all frozen statements and the
audited route.

## Verification evidence

The dependency setup invoked `lake exe cache get`. The whole-Mathlib fetch
encountered repeated HTTP 502 responses and was stopped after the required
dependencies were available. Same-pin local caches supplied missing campaign
modules. The initial bootstrap's missing Mathlib module was repaired, then
the complete 53-module bootstrap retry passed. No dependency revision,
toolchain, or tracked build configuration was changed. No `lake build` was run.

Early scratch development used the same-pin previous-epoch olean tree;
subsequent owned-module checks and the final complete sweep used this
checkout's freshly emitted olean tree. The final gate invokes the committed
`scripts/lean_check_tree.sh` and requires each Lean process to exit zero,
emit no `error:` lines, and produce a fresh olean. It stops at any failure.

- Final sweep: **53/53 pass; zero `error:` lines**.
- Final admitted-declaration warnings: **30**: the one unfinished owned NP
  target, plus 29 out-of-scope declarations.
- `Reductions.lean`: no directly admitted declarations.
- New private helpers: **34/34 admission-free**.
- Owned-file style lint: **0 FAIL, 0 WARN**.
- Statement freeze: **13 existing public declarations unchanged**, both
  ordered signatures and multisets checked; no removals or public additions.
- `git diff --check`: passes.
- Patch replay on a separate index: reproduces the delivered tree exactly.
- Incremental bundle: verifies against the recorded base.

Final sweep tail:

```text
CHECK 51/53 TCSlib/Complexity/Formulas
RESULT 51/53 exit=0 seconds=1.318
CHECK 52/53 TCSlib/Complexity/CookLevin
RESULT 52/53 exit=0 seconds=1.567
CHECK 53/53 TCSlib/Complexity/ClassNP
RESULT 53/53 exit=0 seconds=1.478
PASS: 53/53 modules; seconds=184.992
UTC end: 2026-10-02T22:01:39.191581+00:00
```

### Axiom prints and verified roots

All three headlines currently print
`[propext, sorryAx, Classical.choice, Quot.sound]`. The set alone does not
distinguish a permitted dependency from an unfinished proof; kernel-environment
traversal does:

| Target | Declarations directly using `sorryAx` in its transitive dependency closure | Disposition |
|---|---|---|
| `mem_NP_iff_exists_length_le` | Only `Complexity.mem_NP_iff_exists_length_le` itself | **Unfinished, unsanctioned; continuation required.** |
| `HALT_NPHard` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |
| `HALT_not_mem_NP` | Only `Complexity.NP_subset_EXP` | Sanctioned by the batch brief. |

The traversal inspects checked kernel declarations, both types and values,
including opaque values. It checks every new helper has no direct admission
root and only a subset of `[propext, Classical.choice, Quot.sound]`. The
script deliberately reports the unfinished NP target as such; successful
execution of the diagnostic is **not** a claim that all targets meet the gate.

After recreating the fresh tree, run `verification/run_axioms.sh` with the
checkout path. The full raw results are in `logs/axioms.log`; the verifier
program is included. `verification/sweep.py` and `verification/check_freeze.py`
take the checkout path as their argument. Put the pinned Lean on `PATH`.

## Archive contents and integration

The archive includes this report, continuation instructions, the two full
modified sources, one `git format-patch` patch, an incremental git bundle,
the final sweep and axiom logs, supporting verification scripts/logs, the
committed module order, and `SHA256SUMS`. Every payload file except
`SHA256SUMS` itself is covered.

Verify with `sha256sum -c SHA256SUMS` in the unpacked root. The bundle requires
base `6c09453e6af59ff1575060b66196d28812800d24` and advertises only
`refs/heads/fill/ch2-e2-C`. The patch is suitable for the workflow's `git am -3`
integration, but **must not be mistaken for a completed batch**.

## Brief checklist

- [ ] Three targets filled — **only two are filled**.
- [x] Exercise 2.1 edge-case semantic discharges itemized.
- [x] HALT control-modification lemma named and proved.
- [x] Base hash and all new declarations listed.
- [x] Shared-lemma requests and completion escalation recorded.
- [x] Final full sweep and axiom logs supplied; sanctioned roots checked.
- [ ] Exercise 2.1 has no `sorryAx` — **still open**.
- [x] Diff restricted to owned files and named targets plus private helpers.
- [x] Full sources, patch, bundle, verification material, and checksums supplied.
