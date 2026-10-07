# Chapter 2, epoch 2, batch A — partial continuation delivery

**`NP_subset_EXP` is not yet proved.** This archive uses the brief's explicit
partial-delivery provision. Its outer proof is filled, but it depends on one
openly admitted private construction lemma, `enumMachine_contracts`. The
completed-batch axiom gate therefore remains open.

The delivered implementation proves the exact-width enumeration semantics,
a concrete fixed-width increment-and-rewind machine, a buffered verifier-call
simulator with finite-control output capture and live return, an abstract
timed-loop theorem, and the final exponential-budget normalization. The
concrete initialization, buffer assembly, reset, and loop-controller integration
remain unfinished.

The final fresh sweep passed **53/53 modules, zero `error:` diagnostics**.
There are 40 new source-level private declarations: 38 have no `sorryAx` in
their transitive axiom footprint; the construction lemma and its derived
`enumDecider` depend on the single pending admission. No public declaration
was added or removed.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`
- Required base branch: `complexity/arora-barak-ch1`
- Recorded base: `6c09453e6af59ff1575060b66196d28812800d24`
- Work branch, as instructed by the committed brief: `fill/ch2-e2-A`
- Delivered commit: `a8f26ddb38bc52318282f96b4de6543da0ac03db`
- Delivered tree: `551ea91aa587e74eb8d23583dd028467cd4b7087`
- Binding brief: `briefs/ch2-epoch2-batchA.md` at the recorded base.
- Lean: 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Agent: Codex, single agent, no delegation.

Only `TCSlib/Complexity/ClassNP/EXP.lean` changed in the Git patch. All work
derives from the required base; `main` was not checked out, edited, or used as
a base. There was no push or PR. Report and verification files are archive
artifacts, outside the repository patch.

Initial restricted network access required recovering the exact base objects
through the GitHub connector and checking their Git hashes. A subsequent
successful `git fetch --unshallow origin complexity/arora-barak-ch1` restored
the normal repository history. The delivered bundle has the genuine recorded
base as its prerequisite, not a synthetic snapshot commit.

## Six-contract mapping

All names in this table are private declarations in `Complexity`, except the
public target. **A proved component is not a claim that its surrounding
controller has been constructed.**

| Required contract | Proved evidence | Remaining obligation |
|---|---|---|
| Width evaluation and initialization | `enumWord_length` and `enumWord_zero` identify the exact-width initial word. | No polynomial-width evaluation/initialization machine is yet constructed. Retaining the instance, allocating the candidate, and reaching the initial configuration within the startup bound remain in `enumMachine_contracts`. |
| Fixed-width increment and overflow | `enumInc_spec`, `enumInc_word`, `enumWord_complete`, `enumWord_no_repeat`, and `enumCandidates_iff` prove exact coverage, distinct ranks, and last-rank overflow. `enumCarry_correct` proves an actual one-tape increment and rewind, preserving width with cost at most twice the width plus two. `enumBump_inc` links its result and success flag to `enumInc`. | Embed this subroutine in the final controller and wire overflow to final rejection. Width zero already has one candidate in the enumeration; its increment returns overflow without extending the tape. |
| Buffering, retention, and verifier-call simulation | `enumCaptureCfg`, `enumCapture_step`, and `enumCapture_run` simulate a verifier on an exact prepared buffer. `bufferTape_inputSymbol` and `virtualMove_correct` from the public API supply native reads and clamping, including both boundaries and empty input. The native input head and arbitrary retained tapes/heads are preserved. | Actually assemble `x ++ u` in that buffer before each call and restore its initial position between calls. The simulator theorem assumes the prepared configuration. |
| Capture and return | `enumCaptureTM` suppresses every source emission and records the first bit. `enumCapture_returns` proves return within the verifier budget plus one step, into a live controller state selected using the updated captured bit. It preserves the entire completed source configuration and has empty physical output, including when the bit is emitted on the halting action. | Supply the final controller and its single final-answer emission. Repeated-call correctness also requires the missing reset. No claim is made that two calls have already been composed into a working enumerator. |
| Restart | The call result identifies the full source work tapes and heads, buffer head, retained data, and captured register, making the reset input precise. | No reset-machine theorem is supplied. Clear the bounded visited region, restore all simulated heads and source control, clear the captured bit, restore the buffer/head bookkeeping, and prove a polynomial bound. |
| Timed loop invariant | `enumLoop_run` composes bounded accept-or-advance segments, tests the final candidate before exhaustion, and proves the singleton-output result and total step bound. `enumAny_certificates` identifies the answer with exact-width existential certificates. `enumExponent_bound` and `enumBudget_bound` prove the pointwise EXP bound, including small lengths. `enumDecider` and `NP_subset_EXP` carry out the outer reduction. | The per-round configuration equalities and startup premises for the concrete finite enumerator remain in `enumMachine_contracts`. Thus `enumDecider` and the public target still inherit `sorryAx`. |

## Exact continuation frontier

The only **new directly admitted** declaration is
`Complexity.enumMachine_contracts`, at source line 750. Its statement requires
one uniform finite machine, a polynomial startup bound, a canonical
configuration for every candidate rank, a halted singleton rejection after
the last rejected candidate, and polynomially bounded accept-or-advance
segments on all exact-width candidates.

The contract quantifies over the actual verifier machine and its explicit
polynomial time guarantee. It does not use an untimed composition theorem or
an abstract, potentially noncomputable width function. The certificate width
is exactly the prescribed formula throughout.

Recommended continuation order:

1. Construct the width evaluator and initial candidate with retained input,
   and prove the startup configuration and polynomial cost.
2. Implement buffer assembly and its rewind to the source's initial position.
3. Implement bounded clearing and reset. The existing public
   `Turing.FinTM.source_bounds` in `TuringMachine/Sweep.lean` bounds source heads
   and nonblank cells by elapsed time, but does not itself perform this reset.
4. Instantiate the finite controller of `enumCaptureTM`, integrate the
   increment subroutine, and establish the per-round equalities required by
   `enumMachine_contracts`. Its controller has access to all tape blocks;
   the existing capture lemmas concern `runFrom` on prepared configurations,
   not initialization from its `q₀`.
5. Fill that one admission and rerun the full sweep and axiom checks. The
   already checked outer proof then gives the target.

The public target's original proof sketch and attribution are preserved.
One **Partial-fill appendix** was appended to its docstring to disclose the
remaining admission. The original proof-body `sorry` was replaced by the
outer derivation; this is not a reduction in the number of unfinished
mathematical obligations.

## New declarations

These are all 40 source-level additions, all private. The full statements and
proofs are in the supplied source; compiler-generated auxiliary declarations
are included in transitive dependency checks.

| Name | Role |
|---|---|
| `enumValue` | Little-endian value including high zero bits. |
| `enumInc` | Fixed-width increment with explicit overflow. |
| `enumWord` | Width-preserving representation of a rank. |
| `enumValue_lt` | Value lies below the width's power of two. |
| `enumWord_length` | Exact representation width. |
| `enumWord_zero` | Initial all-false candidate. |
| `enumWord_value` | In-range rank is recovered. |
| `enumValue_injective` | Equal-width representation uniqueness. |
| `enumWord_complete` | Every word is represented. |
| `enumInc_spec` | Successor or exact overflow specification. |
| `enumInc_word` | Increment follows consecutive candidate ranks. |
| `enumWord_no_repeat` | No duplicate in-range candidates. |
| `enumCandidates_iff` | Exact-width certificates equal ranked candidates. |
| `enumBump` | Physical carry result and success flag. |
| `enumCarryPos` | Leading true-prefix length. |
| `enumCarryPos_le` | Carry distance is width-bounded. |
| `enumBump_length` | Carry preserves width on success and overflow. |
| `enumBump_inc` | Physical carry result agrees with abstract increment. |
| `enumBuffer_read` | Read at the start of a suffix. |
| `enumBuffer_write` | Replace one bit without changing width. |
| `enumCarryTM` | Concrete increment-and-rewind finite machine. |
| `enumCarryCfg` | Its canonical tape configurations. |
| `enumCarry_step` | One carry transition, including nonwriting overflow. |
| `enumCarry_run` | Complete carry-phase correspondence. |
| `enumCarry_rewind` | Exact rewind time and result. |
| `enumCarry_correct` | Complete increment, linear time, and live return. |
| `enumCaptureTM` | Buffered capture wrapper with arbitrary finite controller. |
| `enumCaptureCfg` | Full virtual-source and retained-data invariant. |
| `enumCapture_step` | One-step simulation and boundary-tag preservation. |
| `enumCapture_run` | Simulation through the first source halt. |
| `enumCapture_transfer` | Live dispatch using the updated bit. |
| `enumCapture_returns` | Timed captured-call result and exact retained configuration. |
| `enumAny` | Abstract consecutive-rank search. |
| `enumAny_iff` | Search correctness over the rank interval. |
| `enumAny_certificates` | Search answer matches the existential certificate condition. |
| `enumLoop_run` | Timed loop composition from per-round contracts. |
| `enumExponent_bound` | Polynomial exponent absorbed into an EXP bound. |
| `enumBudget_bound` | Full round budget normalized to EXP. |
| `enumMachine_contracts` | **Admitted:** remaining concrete construction. |
| `enumDecider` | Derived decider, **dependent on that admission**. |

## Requested shared lemmas and escalations

Requested shared lemmas: **none for this delivery**. Every added helper remains
private; no private declaration from another module is cited.

Escalations: **none**. No obstruction to a frozen statement was found. The
unfinished work is machine construction and verification, not a proposed
statement repair.

## Verification

Setup ran the required `lake exe cache get`, narrowed to the campaign's
Mathlib roots. It completed successfully. No `lake build` was run. A bootstrap
sweep checked all 53 modules before the source edits. Edits were checked with
`lean_check_tree.sh` starting at EXP and continuing through every later module.
An early downstream check suffered a process-level bus error while dependency
cache setup was still active; it was not accepted as verification. Successful
downstream sweeps and the final fresh sweep followed after setup completed.

The final sweep used a new, separate olean tree and the recorded commit. Each
check exited zero and produced a fresh olean. The log has 53 pass markers,
zero `error:` lines, and 32 admitted-declaration warnings across the chapter.
EXP's two direct admissions are the new continuation frontier and the
unchanged out-of-scope `EXP_subset_NEXP`.

Final sweep tail:

```text
CHECK TCSlib/Complexity/CookLevin
PASS TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
PASS TCSlib/Complexity/ClassNP
MODULES_PASSED 53
END_UTC 2026-10-02T22:06:35Z
```

The axiom audit ran against that final fresh tree. The target prints:

```text
'Complexity.NP_subset_EXP' depends on axioms:
[propext, sorryAx, Classical.choice, Quot.sound]
```

The audit checks every new source-level declaration, permits only the standard
triple for the 38 independent declarations, and traverses constant types and
values (including opaque values) to locate directly admitted dependencies.
The target's **only directly admitted dependency root** is
`_private.TCSlib.Complexity.ClassNP.EXP.0.Complexity.enumMachine_contracts`.
It does not depend on any out-of-scope admitted theorem.

`logs/statement-freeze.log` records preservation of all six original public
signatures, their ordered sequence and multiset, and byte-identical original
definitions plus both out-of-scope proofs. Imports and option headers are
unchanged. `git diff --check` passes. The owned-file policy lint reports
zero FAIL and zero WARN; it records the 882-line file as above the 600-line
target. Exclusive file ownership keeps this one target's helpers together.

## Delivery and reproduction

The archive root contains this report, the full modified source at its
repository-relative path, one `git format-patch` patch, an incremental Git
bundle, sweep and axiom logs, verification inputs, and `SHA256SUMS`.

The bundle requires the recorded base and advertises `refs/heads/fill/ch2-e2-A`
at the delivered commit. `git bundle verify` passes. A temporary-index replay
of the patch reproduces the delivered Git tree exactly without touching any
working branch. Intended maintainer integration is `git am -3` against the
campaign branch, preserving authorship; this archive is a **continuation
checkpoint**, not a completed fill for closing the epoch gate.

After unpacking, run `sha256sum -c SHA256SUMS`. With the pinned toolchain on
`PATH` and dependencies initialized, the included scripts take the repository
path as their argument:

```bash
bash verification/full-sweep.sh /path/to/tcslib
bash verification/run-axioms.sh /path/to/tcslib
python3 verification/check-freeze.py /path/to/tcslib
python3 verification/replay-patch.py /path/to/tcslib
```

Both shell scripts honor `TCSLIB_OLEANS` when using a separate fresh tree.
The axiom script deliberately identifies the present result as partial; its
passing audit status certifies the **disclosed dependency footprint**, not
the completed-batch no-`sorryAx` gate.

## Checklist

- [ ] Target fully proved and completed-batch axiom gate satisfied.
- [x] Six-contract table identifies completed components and remaining work.
- [x] Every new source-level declaration listed; all private.
- [x] Exactly one new directly admitted private declaration identified.
- [x] Recorded base, patch, bundle, and full source supplied.
- [x] Final 53-module sweep and axiom-print log supplied.
- [x] Statement freeze and exclusive file ownership checked.
- [x] Requested shared lemmas and escalations recorded.
