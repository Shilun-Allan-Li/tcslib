# §12 fill campaign — Epoch F1, Batch C: the catalog routines and the two wrapper rows (`Build/Catalog.lean`, Part 1 + W1 + W2)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/s12-f1-C`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `f7f4f0f7`), and never rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `fill-s12-f1-C.zip` with `REPORT.md`, the full modified source file, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling **13 of the 32 audited-true statements** in the §12
layer's catalog module: the five seam routines' 11 run/space contracts
(Part 1) plus the two wrapper space rows W1 and W2. The statement gate
closed after a three-round external audit
(`audits/routine-infra-{findings,r2-findings,r3-findings}.md`, summary
`audits/routine-infra-resolutions.md` — read them); the round-1 report
contains **exact movement-count tables** for every routine (quoted below)
verified against a 16,764-case finite model — your proofs formalize
those counts. **The other 19 sorried statements in your file (every
`computesFunInTime_*_spaceUsed` row, `exists_loopTM_spaceUsed`) are epoch
F2's and must remain sorried and untouched.** Two sibling batches fill
`Build/Embed.lean` and `Build/Seam.lean` concurrently — you never touch
those files. In-repo proved precedents: `capture_run`/`captureAction` and
`redirectTM_computes`/`redirectTM_live` (`Build/Wrappers.lean`), the
`Simulation.lean` sweep gadgets, `Cfg.ofWords` (`Build/Convention.lean`).

## Owned file (modify this and nothing else)

`TCSlib/Complexity/TuringMachine/Build/Catalog.lean` — exactly these 13:

**Part 1 — transition inductions from the seam `Cfg.ofWords` (11):**
1. `transferTM_run` 2. `transferTM_spaceUsedByTape`
3. `copyTM_run` 4. `copyTM_spaceUsedByTape`
5. `clearTM_run` 6. `clearTM_spaceUsedByTape`
7. `compareTM_run` 8. `compareTM_spaceUsedByTape`
9. `incrementTM_run_succ` 10. `incrementTM_run_overflow`
11. `incrementTM_spaceUsedByTape`

Each routine is a three-phase sweep (forward scan, one turn, rewind, one
right-entry into the stationary `done`): state the per-phase
configuration invariant as a `private` lemma (position, written prefix,
untouched suffix, phase control), prove it by induction on the scan
depth, and read the run/space contract off its endpoints. The exact
counts and visited intervals are in the inherited table below — your
budgets must land exactly there (the public bounds' slack is noted).

**The wrapper rows (2):**
12. `capture_visitedByTapeHead` (W1) — prefix-by-prefix application of
    the proved `capture_run`: its liveness hypothesis restricts to each
    prefix; the final halting emission is included; no claim past the
    halt.
13. `redirectTM_spaceUsedByTape` (W2) — complete head-trajectory
    agreement: before the source halt the work actions agree; after it
    the source is absorbed and the redirected machine is halted or in
    its stationary live loop — positions agree at **every** time, with
    no halting or output hypothesis.

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine/Build/Catalog`.
- Iterate on your file per edit. Final: your file with **zero `error:`
  lines and exactly 19 `sorry` warnings** (the epoch-F2 rows — list them
  in `REPORT.md` and confirm none moved), then
  `bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine`.
- **Axiom prints**: `#print axioms Turing.<name>` for the 13 filled
  theorems on the final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  no `sorryAx`: your targets must not lean on any F2 row.

## Ground rules (binding)

1. **File ownership.** Only `Build/Catalog.lean`, and only the 13 targets'
   proofs plus `private` helpers. Shared wishes go under "Requested shared
   lemmas" in `REPORT.md` with a `private` local copy. List every new
   declaration — the epoch audit blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere — **including the 19 F2 rows**. Docstring
   sketch appendices allowed, flagged.
3. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
4. No touching sorries outside your 13. 5. Docstrings stay.
6. Precise imports; keep `set_option` headers.
7. **Continuation budget**: 13 mechanical targets. On exhaustion, deliver
   a partial zip whose `REPORT.md` states what is proved, which `private`
   helpers remain `sorry` (allowed **only** in a partial delivery, each
   listed), and the frontier — the maintainer issues a continuation
   brief.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/routine-infra-findings.md`, the exact table (`L` the touched
word's length; `d` compare's first differing or terminating-blank
position, `d ≤ min(|u|,|v|)`; `p` the first `false` position in a
successful increment, `p < L`):

> | Routine/case | Forward moves | Turn | Return moves | Final right-entry | Exact first exit time | Exact final touched-tape visited set |
> |---|---:|---:|---:|---:|---:|---|
> | transfer | `L` | `1` | `L` | `1` | `2L+2 ≤ 3L+3` | integers `[-1,L]`, size `L+2`, on both tapes |
> | copy | `L` | `1` | `L` | `1` | `2L+2 ≤ 3L+3` | integers `[-1,L]`, size `L+2`, on both tapes |
> | clear | `L` | `1` | `L` | `1` | `2L+2` | integers `[-1,L]`, size `L+2` |
> | compare | `d` | `1` | `d` | `1` | `2d+2 ≤ 2 min(|u|,|v|)+2` | integers `[-1,d]`, size `d+2` |
> | increment, success | `p` | `1` | `p` | `1` | `2p+2 ≤ 2L` | integers `[-1,p]`, size `p+2` |
> | increment, overflow | `L` | `1` | `L` | `1` | `2L+2` | integers `[-1,L]`, size `L+2` |

Binding clarifications from the same loop: transfer/copy finish at
`2L+2` — their `3L+3` bounds are **deliberate slack**; compare turns at
`d` in *every* case (equal words, either proper-prefix orientation, empty
words, aliased indices — "the disjunction selects one action per physical
tape, not two sequential moves") and never inspects `min+1`; a successful
increment never visits `p+1`, and `[false]` returns in two steps; clear
detects the left blank before any erased cell can be mistaken for it,
"because erasure proceeds behind the returning head". Equal-prefix
unequal-length comparison reaches the shorter word's blank at `min`, so
`d = min` there. The round-1 A1-A6 adversarial traces (empty transfer in
2 steps with visited `{-1,0}`; `[true]` vs `[true,false]` both
orientations; `[false]` vs `[true]` in 2 steps; self-compare `fst = snd`;
increment on `[]`/`[false]`/`[true,true]`) are the smallest checks — your
invariants must make them instances.

For W1/W2, the round-1 assessments are the routes quoted in the "Owned
file" section; additionally for W2: "the complete head trajectories still
agree" after the halt — state the trajectory-agreement induction, not an
output comparison (no output hypothesis exists).

## Out-of-scope sorries you will see (leave untouched)

**In your own file**: the 17 `computesFunInTime_*_spaceUsed` rows,
`computesFunInTime_cond_spaceUsed`, and `exists_loopTM_spaceUsed`
(epoch F2). Elsewhere: everything in `Build/Embed.lean` (F1A),
`Build/Seam.lean` (F1B), and all chapter-3/4 statement surfaces.

## REPORT.md checklist

- [ ] 13/13 filled (or the partial frontier per ground rule 7); the 19
      F2 rows confirmed untouched and still sorried.
- [ ] Base commit hash; every new `private` declaration listed (the
      per-routine phase invariants expected).
- [ ] The exact-count table reproduced with your proved budgets beside it
      (slack noted where the public bound is looser).
- [ ] Requested shared lemmas — or "none". Escalations — or "none".
- [ ] Final sweep log tail (zero `error:`, exactly 19 `sorry` warnings) +
      facade check + 13 axiom prints (at most the standard triple; no
      `sorryAx`).
- [ ] Diff touches only `Build/Catalog.lean`.

## Known pitfalls at this pin (hard-won)

- The routines' phase types (`SweepPhase`, `FlagPhase`) are small
  inductives: `cases` on the phase, then `dsimp only`, then the step
  equation; keep one `private` invariant lemma per routine rather than
  one monolithic induction.
- Seam endpoints are `Cfg.ofWords`: input position 1, all work heads 0,
  contiguous words from 0, live control, empty output — the invariant's
  base case is definitional.
- Aliased indices in `compareTM` (fst = snd): the transition's
  disjunction produces **one** action on the shared physical tape — do
  not case-split into two moves.
- `Function.update_of_ne` (not `update_noteq`); after
  `cases hs : cfg.state`, `dsimp only` before rewriting; avoid bare
  `simp` with folded forms; `omega` needs beta-reduced,
  non-`Fin`-projection goals.
- Work tapes are ℤ-indexed `Option Symbol` via `Function.update`; the
  `[-1, L]` visited intervals are `Finset.image` facts over
  `Finset.range (t+1)` — build them from the trajectory, not from
  interval arithmetic on bounds (the round-1 R6 lesson: the trajectory
  is `[-1, d]`, not `[-1, min+1]`).
- `capture_run`'s liveness hypothesis is strict-before-`t`: instantiate
  it per prefix, not once globally.
- `redirectTM`'s post-halt behavior splits: halted vs the stationary
  live loop — both are stationary; the trajectory equality does not need
  to know which.
