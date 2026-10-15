# §13 fill campaign — Tranche A-S2, Batch ZF-A3 (continuation): the zone shift machines (`Build/Zone.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Before you start, confirm that
  `git merge-base --is-ancestor 0aea21088db1f8c44d4c1bb5ba57f28eceb3c354 HEAD`
  succeeds. That commit proves the §12.6 framed catalog contracts you will
  cite. If the check fails, **stop**.
- Create your working branch off the campaign branch (suggested name
  `fill/zone-f1-A3`). Record the base commit hash in `REPORT.md`; the brief
  was issued at `4502c30fd24b054834b66b4621f06b91db545ee6`. Never rebase.
- **Delivery is by zip, not PR or push**: `zone-f1-A3.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against
  your recorded base, a git bundle, the final sweep log, the axiom log, and
  `SHA256SUMS`.

## What this is

This is the second continuation of batch ZF-A. Everything in
`briefs/zone-f1-batchA.md` and `briefs/zone-f1-batchA2.md` binds unless
amended here; read both in full. Also read both earlier reports,
`audits/zone-agent-reports/f1-A-REPORT.md` and `f1-A2-REPORT.md`.

**Your targets are the two remaining machine rows:**
`Turing.FinTM.exists_zoneShiftInTM` (first) and
`Turing.FinTM.exists_zoneShiftOutTM` (last). The other 18 targets of
`Build/Zone.lean` are proved and integrated.

**What changed since ZF-A2.** ZF-A2 stopped on a shared-interface gap. Its
report shows that the canonical catalog contracts do not cover a delimited
word at displaced heads inside a larger tape, and includes a kernel-checked
regression in which a bare transfer erases a cell of the next zone. **That
gap is closed.** Design §12.6 added five framed contracts to
`Build/Catalog.lean`. They passed a statement gate and are proved (integrated
at `0aea2108`; the fill gate has closed):

| Contract | Exact time | Trajectory |
|---|---|---|
| `Turing.transferTM_run_ofCfg` | `2|w| + 2` | both touched heads in `[pos − 1, pos + |w|]` |
| `Turing.copyTM_run_ofCfg` | `2|w| + 2` | as transfer |
| `Turing.clearTM_run_ofCfg` | `2|w| + 2` | `[pos − 1, pos + |w|]` |
| `Turing.incrementTM_run_succ_ofCfg` | `2p + 2`, where `p = (w.takeWhile id).length` | `[pos − 1, pos + p]` |
| `Turing.incrementTM_run_overflow_ofCfg` | `2|w| + 2` | `[pos − 1, pos + |w|]` |

Each holds from an **arbitrary** configuration whose touched tape carries the
word `w` with blanks at relative positions `−1` and `|w|`. Each gives:

- the exact finish configuration at the exact time: every other cell, every
  head, the input position and the output unchanged;
- no earlier arrival at the live exit anchor;
- the trajectory bound above, with every untouched head fixed.

The increment success time is **carry-sensitive**, which resolves ZF-A2's
caution that `incrementTM_run_succ` exposes only the loose `2|w| + 2`.

## Owned file (modify this and nothing else)

`Build/Zone.lean`: the two target proofs plus new `private` helpers. The 18
proved targets and the 16 existing private declarations are **frozen and
byte-identical**. That includes ZF-A2's seven staging lemmas
(`zoneStageWord`, `zoneStageWord_length`, `zoneStageWord_getElem`,
`zoneStageSlot`, `zoneStage_rightWindow`, `zoneStage_leftWindow`,
`zoneStage_window_bounds`), which you may consume. **No import changes**:
`Zone.lean` already imports `Simulation`, `Build/Embed`, `Build/Seam` and
`Build/Catalog`.

## Ground rules (binding)

1. **Statement freeze**: no renames, re-signatures, restatements, or
   attribution edits. Docstring sketch appendices are allowed if flagged.
2. **Construction reuse**: assemble the rows from the §12 layer by
   **citing its public exports**, never re-deriving them. A private copy of
   any Catalog, Embed, Seam, Loop or Primitives declaration will be rejected
   at integration. Zone-specific glue is new work, not a copy:
   - the small finite-control machines for navigation steps, boundary
     save/restore, guard tests and the final halt;
   - their run lemmas;
   - the window bookkeeping.
3. **Cite only proved contracts.** `Build/CounterLoop.lean` (§12.7,
   decrement and counter-driven loops) is **statements only**. It is not
   imported, and you must not use it. The statement gate's own route needs no
   decrement: increment-to-overflow implements the distance countdown (see
   the obligations below).
4. **One proof per shared phase.** The inward and outward rows, and the two
   sides of each, share navigation, window location, boundary preparation
   and staging. Prove each shared phase **once**, as a private lemma
   parameterized by side or direction. Do not restate it per row; restating
   is how earlier batches grew copies.
5. **Escalation**: on anything unprovable as stated, stop, record it, and
   deliver what exists. If a public contract genuinely cannot express a
   needed framed run, request **one public shared lemma** for the
   appropriate §12 file under "Requested shared lemmas" rather than copying.
   ZF-A2's escalation is the model.
6. **Continuation budget**: the inward row first. A complete inward row beats
   two partial rows.

## The binding implementation notes (round-1/round-3 statement audits, verbatim from the original brief)

> The level is an input to one fixed machine, not a finite-control
> parameter. A direct implementation tests the lower guard, stages the
> affected words on tape 1, and rewrites the two adjacent windows. Word
> ends are distinguishable because a stored virtual blank occupies two
> nonblank false cells. Staging may copy the whole two-zone window; its
> size is still `O(2^i)`. A false guard returns the original tape and
> scratch word unchanged. Navigation counters and boundaries must be
> implemented with a geometric total ledger, rather than performing an
> `i`-cell counter scan for every cell moved — counting down a binary
> power of two with its least significant bit anchored has total
> carry/borrow work `Σ_{r=1}^{2^i}(1 + v₂(r)) < 2^(i+1)`; initializing
> the counter from unary `i` costs a polynomial in `i`, absorbed by
> `O(2^i)`. Bounded staging can use reserved invalid pair codes as
> temporary delimiters, saving overwritten boundary pairs in finite
> control and restoring them. The affected data window lies in
> `[−2·zoneBase(i+1), 2·zoneBase(i+1)+1]`, inside the row's interval;
> scratch is bounded separately. Every finite pass has a bounded stopping
> condition; cleanup restores the unary level and both heads; choosing
> the first halt time supplies the no-earlier-halt clause, positive
> because the initial state is live.

## The consumer obligations (the §12.6 statement gate, finding F7; verbatim)

These come from `audits/s12-framed-findings.md`, "Fitness for the zone
consumer"; read the whole section.

> **Boundary preparation is feasible with two tapes.** Each saved boundary
> value lies in `Option Bool`, so saving two delimiters requires only nine
> possible symbol pairs in finite control, independently of the zone level
> and word length. The controller must locate those cells, save their
> values, install blanks, return to the word's starting head, invoke the
> routine, and restore the saved values afterward. The machines never write
> the delimiter cells; the contracts preserve them at exit and return the
> heads exactly, including for empty words. Coordinates are recovered by the
> navigation procedure; no unbounded coordinate is stored in finite control.
> Protect the other scratch intervals, including the unary level word, as
> part of the outer frame.

> **Left-side orientation needs explicit bookkeeping.**
> `zoneStage_leftWindow` reads away from home in decreasing coordinates,
> whereas these routines sweep toward increasing coordinates. Starting at
> the leftmost occupied physical cell therefore supplies
> `reverse (zoneStageWord false …)` to the framed contract. The controller
> must account for that reversal when staging and placing words. A
> reflected-machine contract is not required if both calls use the
> appropriate ascending physical representation; the existing left-window
> lemma alone is not a reflected-run theorem.

> **Carry-sensitive time supplies the geometric ledger.** Use an `i`-bit
> zero counter and stop on its first overflow after `2^i` increments. For
> increment number `r < 2^i`, the old word has exactly `v₂(r)` initial true
> bits; at `r = 2^i`, the overflow cost is also `2v₂(r) + 2 = 2i + 2`. …
> `Σ_{r=1}^{2^i}(2v₂(r) + 2) = 2^{i+2} − 2`. This includes `i = 0`: the
> empty counter overflows in two steps. … The counter delimiters should
> remain installed across the run; initialization, later cleanup, and
> restoration are charged separately. Increment-to-overflow can implement
> the required distance countdown without a new decrement contract. The
> consumer must still prove that its actual counter schedule, rather than an
> arbitrary sequence of counter resets, has this cost.

> **Remaining consumer obligations, not missing catalog statements:**
> uniform finite control independent of `i`; window location;
> source-boundary preparation/restoration; left-side word orientation; the
> guarded identity branch; exact unary-scratch restoration; composition and
> first-return transport; and an explicit transition to genuine halt.

**Where the counter lives (guidance, checked against the contracts).**
- **It must live on tape 1, beside the level word.** `copyTM` and
  `transferTM` move words **between distinct tapes** (`hne : src ≠ dst`),
  never within one, and tape 0 has no guaranteed free region near home.
- **It cannot be the level word itself.** An overflow leaves its word all
  `false`, no proved catalog routine rewrites `false` cells back to `true`,
  and the row must end with exactly `bufferTape (List.replicate i true)` on
  tape 1.
- **Build it with zone-specific glue.** The binding note allows an
  initialization polynomial in `i`. For example, a zigzag can mark one
  level cell at a time and append one `false` to an `i`-bit word placed past
  the level word's right blank, then restore the marks. This is `O(i²)`
  steps, absorbed by `c · (2^i + i + 1)`.
- **Run and remove it with catalog routines.** Count with
  `incrementTM_run_succ_ofCfg` and `incrementTM_run_overflow_ofCfg`; the
  counter's delimiters are the level word's right blank and the cell past
  the counter. Remove it with `clearTM_run_ofCfg` at its displaced head.

## Assembly (guidance; the obligations above are binding)

| Phase or obligation | Public exports to consume |
|---|---|
| Staging, counter initialization and cleanup at displaced heads | `transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg` (`Build/Catalog`), with their trajectory clauses for the interval and space clauses |
| Space of a phase from its trajectory | `MultiTapeTM.spaceUsedByTape_le_card_Icc` (this file) |
| Sequencing at live anchors, from arbitrary configurations | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg` (`Build/Seam`) |
| A positive call that starts and ends at one anchor | `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead` (`Build/Seam`). These return to a **live** anchor and are not a halting adapter |
| The final halt | Supply it explicitly: a final glue state whose transition halts, joined by a seam, and take the first halt time for the row's no-earlier-halt clause |
| Window facts | ZF-A2's staging lemmas and `zoneStage_window_bounds` (this file); `zoneIndex_eq_iff`, `zoneBase_succ` |

All catalog routines are `k`-tape machines indexed by tape, so they run
directly on the row's two tapes; no tape embedding is needed. The catalog's
canonical `Cfg.ofWords` contracts do **not** apply on a zoned tape. Use the
`_ofCfg` forms throughout.

## Duplication governance (binding)

Run the text-level screen before and after:

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/Zone.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean \
  TCSlib/Complexity/TuringMachine/Build/Seam.lean \
  TCSlib/Complexity/TuringMachine/Build/Embed.lean
```

It lists every like-kind pair in which one declaration reproduces at least
half of another's extracted body. The rules:

- **No new pair may have a `Zone.lean` declaration on one side and a
  declaration of another file on the other.** That would be a copied
  catalog, seam or embedding proof.
- **List every new in-file pair among your declarations** in `REPORT.md`,
  with a one-line justification. A pair at 90% or more is a copy; factor it
  into one shared lemma (ground rule 4).

Quote both outputs, before and after. `REPORT.md` carries the ledger line
"new copies: none", with each phase's §12 citations named.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- Bootstrap: the standard order list, then `Build/Embed`, `Build/Seam`,
  `Build/Catalog`, `Build/VirtualInput`, `Build/Zone`.
- Final: `Build/Zone` with **zero errors and zero sorry warnings**, and the
  `TuringMachine` facade with zero errors. `Zone.lean` is not yet in the
  facade, so check it directly.
- **Axiom prints for all 20 targets**, re-printing the 18 integrated ones: at
  most `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`.
- Lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  must report 0 FAIL. `Zone.lean`'s size WARN is justified in the plan's
  decision log ("A-S2 fill epoch: ZF-A and ZF-C partials INTEGRATED");
  cite it.

## REPORT.md checklist

- [ ] 2/2, or the inward row plus a frontier; the base hash and the ancestor
      check.
- [ ] Every new `private` listed with its role; requested shared lemmas, or
      "none".
- [ ] The phase decomposition of each row, with each phase's §12 citations
      and its time, interval and scratch-space contributions.
- [ ] The counter's schedule, and its geometric cost proof.
- [ ] Duplication: the copy-text screen before and after, every new in-file
      pair justified, and "new copies: none".
- [ ] Final sweep tail, the 20 axiom prints, and the lint line.
- [ ] Diff touches only `Build/Zone.lean`.

## Known pitfalls at this pin (hard-won)

- **The zoned tape is not `Cfg.ofWords`.** Every catalog call needs its
  framed hypothesis: the word at the head, with blanks at relative `−1` and
  `|w|`. Inside a zone, those delimiter cells usually hold data. Save,
  blank, call and restore them; ZF-A2's regression is the failure mode.
- **Left-side words are reversed** relative to the ascending sweep (F7
  above). Decide once, in a shared lemma, how each side's window is
  presented to the catalog.
- **The catalog routines exit at live anchors** (`done`, `done b`). Neither
  they nor `seamReleaseTM` halt. The row's halt is yours to add.
- **Through-halt contracts** need `(hc : c.state ≠ none)`, equivalently
  `0 < T`. A zero-time run of an initially halted configuration is the
  standard trap (the §12 round-2 blocker).
- **The identity branch must hold for arbitrary outer contents**, including
  a false guard at a level whose zones are full or cramped.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; feed
  `omega` the `Nat.two_pow_pos`/`pow_succ` facts it cannot see.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
