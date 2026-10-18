# Ch2 fill campaign — Epoch 2, Batch C: Exercise 2.1 and the HALT pair

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch1`** — this exact branch, NOT
  `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/ch2-e2-C`), record
  the base commit hash in `REPORT.md`.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-ch2-e2-C.zip` with `REPORT.md`, the full modified sources, the
  `git format-patch` series, a git bundle, the final sweep log, the
  axiom-print log, and `SHA256SUMS`.

## Context

Three targets. **Exercise 2.1** (`mem_NP_iff_exists_length_le`) is the
audited equivalence between the exact-length concatenation form of `NP` and
the bounded-length paired form — its reverse construction was built *by the
auditor* across three rounds and transcribed into the docstring; your job is
to follow it, not redesign it. The **HALT pair** rides on `NP_subset_EXP`
(batch 2A, concurrent — see the sanctioned-dependency rule below): hardness
by embedding one fixed code via the audited control-modification recipe, and
non-membership by the decidability contradiction. Epoch 1's calculus
(`compl_mem_P`, `mem_P_of_polyTimeReducible`, …) and Chapter 1's machines
(`one_work_tape_binary`, `exists_codeTM`, `pairEncode` machinery) are proved
and at your disposal.

## Owned files (modify these and nothing else)

- `TCSlib/Complexity/ClassNP/NP.lean` — `mem_NP_iff_exists_length_le`
  (line 131, 8 pts) **only**.
- `TCSlib/Complexity/ClassNP/Reductions.lean` — `HALT_NPHard` (line 180,
  6 pts) and `HALT_not_mem_NP` (line 206, 4 pts) **only**.

## Environment and verification

As the epoch-1 briefs: pinned toolchain; `lake exe cache get` once; **never
`lake build`**; bootstrap the 53-module list; iterate per owned module plus
the later modules; final full sweep, zero `error:` lines.
**Axiom prints**: at most `[propext, Classical.choice, Quot.sound]`
(subsets fine — disposition D1). **Sanctioned `sorryAx`, this batch only:**
`HALT_NPHard` and `HALT_not_mem_NP` may show `sorryAx` **solely** through
`Complexity.NP_subset_EXP` (batch 2A's concurrent target — rely on its
frozen statement; at epoch merge the dependency closes, as epoch 1's did).
`mem_NP_iff_exists_length_le` must be clean. Any other `sorryAx` root is a
defect; verify the root as batch E1-A did (kernel-environment traversal or
equivalent) and say so in `REPORT.md`.

## Ground rules (binding)

Identical to epoch 1 (`workflow.md` §4): exclusive ownership, named targets
only; `private` helpers, all listed; statement freeze, escalation over
alteration; no out-of-scope sorries; docstrings stay; precise imports.
Combined 18 points — continuation per the B2 precedent if needed.

## Targets and their binding routes

1. **`mem_NP_iff_exists_length_le`** (NP.lean:131). The docstring carries
   the full audited construction; it is binding, in particular:
   - (⇒) the paired verifier with the **same** bound; the `pairDecode`
     grammar scan; the length-equality check against the explicit formula.
   - (⇐) exact length `R n = (C+1)(n+1)^c` — this coefficient/degree choice
     is the **repaired** one (round-2 finding 1 refuted `C(n+1)^c + 1`);
     the marker/strip discipline: pad to `u ++ [true] ++ false-run`, split
     at the **last** `true`, and *reject when no length-equation solution
     exists* (round-3 finding 1 — e.g. `y = []`).
   - Inherited verbatim from `audits/ch2-phase1-round3-findings.md`:
     > These checks also show why the original-bound test remains
     > necessary: the larger region can contain a marker after too many
     > witness bits. Merely fitting inside `R(n)` does not authorize that
     > witness.
     So the verifier **must** re-check `|u| ≤ C(n+1)^c` after stripping.
   - The audited edge cases to keep provable: `C = 0`, `c = 0`, `x = []`,
     `u = []`, all-`false` region, malformed strings.
2. **`HALT_NPHard`** (Reductions.lean:180). The docstring's four-step
   repaired construction (finding 6) is binding: total exponential decider
   from `NP_subset_EXP` (statement; sorried until merge) →
   `one_work_tape_binary` (legal: total) → the control modification
   (remember the emitted bit **including a bit emitted on the halting
   transition**; halt iff `true`, else enter the stationary live loop) with
   its own run/halting lemma → `exists_codeTM`, fixed `α`, and the
   emit-then-copy prefix machine (`2|α| + |x| + 3` steps; `pairDiagTM` is
   the diagonal precedent, not this function). Only
   `Turing.MachineCode.decode_encode` may be used of the scheme — the
   statement quantifies over **every** `MachineCode`.
3. **`HALT_not_mem_NP`** (Reductions.lean:206). The decidability
   contradiction chain exactly as sketched; note the docstring's
   **proof-route restriction** paragraph is load-bearing audit history —
   do not "improve" the statement's generality (that is a recorded
   human-review question, not a fill decision).

## Out-of-scope sorries you will see (leave untouched)

`NP_subset_EXP`, `EXP_subset_NEXP` (EXP.lean — 2A / epoch 3); the
`Nondeterminism.lean` compilations and padding cluster (2B / epoch 3); the
`TMSAT.lean` four (2D); everything in E3/E4.

## REPORT.md checklist

- [ ] Three targets filled; for Ex 2.1, a line per audited edge case saying
      where it is discharged; for HALT, the control-modification lemma
      named.
- [ ] Base hash recorded; new declarations listed.
- [ ] Requested shared lemmas / escalations — or "none".
- [ ] Final sweep log tail + axiom prints, with the two sanctioned
      `NP_subset_EXP`-rooted `sorryAx` cases called out and root-verified.
- [ ] Diff touches only the two owned files, only the named targets.

## Known pitfalls at this pin

The epoch-1 list carries over verbatim (see
`briefs/ch2-epoch1-batchA.md` §pitfalls, same pin), plus:
- `pairEncode`/`pairDecode`: the doubled-prefix grammar is Chapter 1's;
  its proved lemmas (`pairEncode_injective`, `decode_encode`,
  `HALT_pairEncode_eq_true_iff`) are the citable API — do not re-derive.
- Splitting at the **last** `true`: `List.getLast?`/reverse-find patterns
  need care with `beq` vs `=`; keep the strip function `private` with its
  own spec lemma.
- `n ↦ n + R n` strict monotonicity is the uniqueness engine for the
  split search — prove it once, `private`, reuse in both directions.
- The stationary live loop state: one state, no emission, no movement,
  same state — its non-halting run lemma is two lines by induction; don't
  entangle it with the capture machinery.
