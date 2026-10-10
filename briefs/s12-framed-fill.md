# §12.6 fill — the five framed catalog contracts (`Build/Catalog.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/s12-framed`).
  Record the base commit hash in `REPORT.md`; the brief was issued at
  `841122fc6d39657f764e5b46e9756121e98e879e`. Never rebase.
- **Delivery is by zip, not PR or push**: `s12-framed-fill.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against
  your recorded base, a git bundle, the final sweep log, the axiom log, and
  `SHA256SUMS`.

## What this is

Fill the **five audited-true statements** of design §12.6
(`machine-library-design.md` §12.6; gate closed round 1 with no findings, see
`audits/s12-framed-findings.md` and `audits/s12-framed-resolutions.md`, and
read both in full):

| Target | Exact time |
|---|---|
| `Turing.transferTM_run_ofCfg` | `2|w| + 2` |
| `Turing.copyTM_run_ofCfg` | `2|w| + 2` |
| `Turing.clearTM_run_ofCfg` | `2|w| + 2` |
| `Turing.incrementTM_run_succ_ofCfg` | carry-sensitive `2p + 2`, where `p = (w.takeWhile id).length` |
| `Turing.incrementTM_run_overflow_ofCfg` | `2|w| + 2` |

Each holds from an **arbitrary** configuration whose touched tape carries a
word delimited by blanks at relative positions `-1` and `|w|`. It gives the
exact finish configuration, excludes earlier exits, and bounds the
trajectory. These contracts unblock the zone shift machines (ZF-A3). Their
consumer is `Build/Zone.lean`; you do not touch it.

## Owned file (modify this and nothing else)

`Build/Catalog.lean`, the R3 section only: the five §12.6 targets, the five
canonical R3 run rows, and the R3 private trace lemmas
(`catalogCfg`/`catalogTrace`/`catalog_trace_run`, the
`catalogClear*`/`Copy*`/`Transfer*`/`Inc*` traces, and their lemmas, all
local to that section).

## The central rule: one generalized trace per routine (binding)

The gate's guidance, verbatim from the findings: "During fill, generalize the
existing traces in their shared home and derive the canonical rows by
specialization. Preserve theorem statements; avoid parallel private copies
of the same traces."

1. **Generalize, don't duplicate.** Prove each routine's forward/turn/rewind
   trace once, for the framed configuration. The existing private traces
   assume canonical `catalogCfg` words and origin heads. **Replace** them
   with framed generalizations; **do not keep both**. `catalog_trace_run`
   is already generic over `F R D`, so reuse it as is. The `compareTM`
   traces stay, because compare is not framed.
2. **Re-derive the canonical rows.** Replace the proof bodies of
   `transferTM_run`, `copyTM_run`, `clearTM_run`, `incrementTM_run_succ` and
   `incrementTM_run_overflow` with specializations of the framed contracts
   at `d := Cfg.ofWords …`. **These five public proof-body swaps are
   sanctioned.** The statements stay byte-identical. The specialization
   argument is in the findings' "Canonical specialization" table:
   - the time `2n+2 ≤ 3n+3` (or `2p+2 ≤ 2n+2`);
   - the finish configuration is extensionally the canonical
     `Cfg.ofWords` finish;
   - the canonical blank-destination premise makes the destination's old
     suffix vanish;
   - `incFixed` preserves width.

   The four `_spaceUsedByTape` rows may stay as they are, or be re-derived
   from the framed trajectory clause through
   `MultiTapeTM.spaceUsedByTape_le_card_Icc`. Your choice; disclose it.
3. **Reorder as needed.** The framed section currently sits after the
   canonical rows. Moving it, or the generalized traces, above the canonical
   rows is **sanctioned** so that the canonical proofs can cite it. Flag the
   move; every statement stays byte-identical.
4. **Net private declarations must not increase.** Each generalized trace
   replaces its canonical predecessor. Report the private delta.

## Ground rules (binding)

1. **Statement freeze** on every public declaration of `Catalog.lean`. The
   only exceptions are the five sanctioned canonical proof bodies above and
   the flagged reordering.
2. **Duplication**: zero new copies. Run
   `python3 -I audits/evidence/retrofit/r1-public-proof-screen.py <repo-root>`
   (about three minutes) before and after, and quote pass 4's file totals.
   **No file's member count may increase.** Catalog is the most-copied file
   in the tree.
3. **Out of scope:** `compareTM` framing, any new machine (such as the
   decrement routine ZF-B3 requested), and every other part of Catalog.
4. **Escalation** on anything unprovable as stated; never restate.

## Proof route (from the gate's findings; binding)

Use the trace inductions in the findings ("Transition-based justification" and
"Every-time trajectory and frame"):

- **Forward phase**, `0 ≤ t ≤ m`: relative offset `t`; the destination
  prefix `[0,t)` has been written.
- **Turn** at the source's right blank, then **return**: offset `2m − t`
  for `m+1 ≤ t ≤ 2m+1`; transfer and clear erase the suffix `[n−r, n)`.
- **Entry** at the left blank, at `T = 2m+2`.

Here `m = n` for the three sweep contracts and for overflow, and `m = p` for
a successful increment. Use `incFixed`'s characterization:
`incFixed w = some v` gives
`w = replicate p true ++ false :: rest` and
`v = replicate p false ++ true :: rest`, with `p < n` and `|v| = n`;
`incFixed w = none` holds iff `w = replicate n true`.

`Action.apply` writes at the old head, then moves. Inactive tapes receive
`(none, 0)`, and the input movement is `0` with no output, at every step.

## Optional permanent regressions (audit-adopted; flagged)

The findings' 15 concrete cases (T1–T3, C1–C3, E1–E3, S1–S3, O1–O3) as kernel
`decide`/`rfl` checks, width preservation of `incFixed`, and the two `incFixed`
branch characterizations as standalone lemmas.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- Final: `Build/Catalog` with **zero errors and zero sorry warnings**. Then
  `Build/Zone`, `Codes2Tape` and the `TuringMachine` facade with zero
  errors (their own admissions are baseline; list them).
- **Axiom prints** for the five framed and the five canonical run rows: at
  most `[propext, Classical.choice, Quot.sound]`, no `sorryAx`. Also every
  other public Catalog declaration, byte-identical to baseline.
- Lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  must report 0 FAIL.

## REPORT.md checklist

- [ ] 5/5, or a frontier; base hash; the reordering, if any, flagged.
- [ ] The five canonical proof-body swaps listed, each now citing its framed
      contract; the space rows' disposition.
- [ ] The private delta (must not increase); every replaced or new private
      listed.
- [ ] Census before/after (pass 4 file totals; none may increase).
- [ ] Final sweep tail, the axiom prints, and the lint line.
- [ ] Diff touches only `Build/Catalog.lean`.

## Known pitfalls at this pin (hard-won)

- Negative coordinates: the finish expressions use `q - d.workTapePos j`
  (relative offsets in `ℤ`), so never route through `Int.toNat`.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; avoid
  bare `simp` on folded forms.
- `Finset.Icc` on `ℤ` is available (`Int.card_Icc`); on `ℕ` it is not in
  this import closure.
- The canonical blank-destination premise `hdst : w dst = []` is what kills
  the destination's old suffix in the specialization; don't drop it.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
