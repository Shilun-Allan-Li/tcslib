# §13 fill campaign — Tranche A-S2, Batch ZF-A2 (continuation): the zone shift machines (`Build/Zone.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/zone-f1-A2`).
  Record the base commit hash in `REPORT.md`; the brief was issued at
  `f171767f32e573c345f3fa9b6e9fb87e14b84ddf`. Never rebase.
- **Delivery is by zip, not PR or push**: `zone-f1-A2.zip`, containing
  `REPORT.md`, the full modified source, a `git format-patch` series against
  your recorded base, a git bundle, the final sweep log, the axiom log, and
  `SHA256SUMS`.

## What this is

This is a continuation of batch ZF-A (`briefs/zone-f1-batchA.md`; read it
in full, since everything there binds unless amended here). ZF-A proved 18
of the 20 targets of `Build/Zone.lean`, and they are integrated. Its report
is `audits/zone-agent-reports/f1-A-REPORT.md`; read it, in particular its
continuation map. **Your targets are the two remaining machine rows:**
`Turing.FinTM.exists_zoneShiftInTM` (first) and
`Turing.FinTM.exists_zoneShiftOutTM` (last).

ZF-A stopped on a scope defect in the original brief. The brief required
the rows to be assembled from the §12 layer, but `Zone.lean` does not import
it. **That is now resolved (user decision, 2026-10-10).** You may add exactly
these three imports to `Zone.lean`, and must flag them in `REPORT.md`:

```lean
import TCSlib.Complexity.TuringMachine.Build.Embed
import TCSlib.Complexity.TuringMachine.Build.Seam
import TCSlib.Complexity.TuringMachine.Build.Catalog
```

Nothing in the repository imports `Zone.lean`, so these cannot create a
cycle. No other import changes are allowed.

## Owned file (modify this and nothing else)

`Build/Zone.lean`: the two target proofs plus new `private` helpers. The 18
proved targets and the 9 existing private lemmas are **frozen and
byte-identical**; you may consume them.

## Ground rules (binding)

1. **Statement freeze**: no renames, re-signatures, restatements, or
   attribution edits. Docstring sketch appendices are allowed if flagged.
2. **Construction reuse**: the rows are **assembled from the §12 layer by
   citation of its public exports**, never re-derived. `Build/Catalog.lean`
   is already 70% copied material (`audits/duplication-ledger.md`); **a
   private copy of any Catalog, Embed, Seam, Loop or Primitives declaration
   will be rejected at integration**. `REPORT.md` carries the ledger line,
   "new copies: none", with each phase's §12 citations named.
3. **Escalation**: on anything unprovable as stated, stop, record it, and
   deliver what exists. If the general-configuration contracts genuinely
   cannot express a needed framed run, request **one public shared lemma**
   for the appropriate §12 file under "Requested shared lemmas", rather
   than copying.
4. **Continuation budget**: the inward row first. A complete inward row
   beats two partial rows.

## The binding implementation notes (round-1/round-3 audits, verbatim from the original brief)

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

## ZF-A's continuation map (from its report; the obligations are binding, the export table is guidance)

Obligations:

1. Uniform unary-level navigation with the anchored binary-countdown
   geometric ledger; no level baked into finite control.
2. Bounded guard tests, pair-preserving staging, and word-window rewrites,
   including identity branches and arbitrary outer tape contents.
3. Scratch cleanup to `bufferTape (List.replicate i true)`, both heads at
   zero, input position preserved, output empty, and the first-halt cut.
4. Data-head interval containment and the separate scratch-space bound,
   then one common coefficient for time and scratch.

| Phase/obligation | Public exports to consume |
|---|---|
| Transfer/copy staging and cleanup | `transferTM_run`, `transferTM_spaceUsedByTape`, `copyTM_run`, `clearTM_run`, `clearTM_spaceUsedByTape` (`Build/Catalog`) |
| Returning embedding and trajectory transport | `embedEmitRetTM_run`, `embedEmitRetTM_visitedByTapeHead` (`Build/Embed`); the silent counterpart needs a separate capture tape |
| General-configuration sequencing | `seamCompTM_run_ofCfg`, `seamCompTM_firstReturn_ofCfg`, `seamCompTM_visitedByTapeHead_ofCfg` (`Build/Seam`) |
| Release to genuine halt | `seamReleaseTM_firstReturn`, `seamReleaseTM_visitedByTapeHead` (`Build/Seam`) |

ZF-A's caution is binding. The catalog's canonical word-run contracts do
**not** automatically give framed, displaced runs on a two-sided zoned tape.
Connect the window invariants explicitly to the general-configuration and
embedding contracts, and never assert a missing adapter without proof.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**. Use `scripts/lean_check_tree.sh` for every check.
- Bootstrap: the standard order list, then `Build/Embed`, `Build/Seam`,
  `Build/Catalog`, `Build/VirtualInput`, `Build/Zone`.
- Final: `Build/Zone` with **zero errors and zero sorry warnings**; the
  `TuringMachine` facade with zero errors. `Zone.lean` is not yet
  facade-wired, so check it directly.
- **Axiom prints for all 20 targets** (the 18 integrated ones re-printed):
  at most `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Lint: `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  must report 0 FAIL. `Zone.lean`'s size WARN is justified in the plan's
  decision log; cite it.

## REPORT.md checklist

- [ ] 2/2, or the inward row plus a frontier; base hash; the three
      imports flagged.
- [ ] Every new `private` listed with its role; requested shared lemmas,
      or "none".
- [ ] Duplication ledger: "new copies: none", with the §12 citations per
      phase.
- [ ] Final sweep tail, 20 axiom prints, and the lint line.
- [ ] Diff touches only `Build/Zone.lean`.

## Known pitfalls at this pin (hard-won)

- The zoned tape is not `Cfg.ofWords`. Use the general-configuration
  (`_ofCfg`) seam forms throughout.
- The `bufferTape` level word on tape 1 follows the §12 loop host's fuel
  discipline. Cite the public loop exports; never copy `f2_loopHost_*`.
- Through-halt contracts need `(hc : c.state ≠ none)`, equivalently
  `0 < T`. A zero-time run of an initially halted configuration is the
  standard trap (the §12 round-2 blocker).
- `Function.update_of_ne`; `dsimp only` after `cases` on control; feed
  `omega` the `Nat.two_pow_pos`/`pow_succ` facts it cannot see.
- The style linter requires a literal "Proof sketch" before **every**
  `sorry`; this matters only for a partial delivery.
