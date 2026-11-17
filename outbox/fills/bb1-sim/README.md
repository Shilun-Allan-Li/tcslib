# Claude fill `bb1-sim` (pairings T2 `bb1_sim_real`, T3 `bb1_sim_random`, and the `Games/Relational` targets)

Claude is the worker, a lead with up to 2 sub-agents on disjoint files (standing ruling: Claude for fills). The job is
the fill phase of design r1 (`../design-r1.md` §4.2) under Seyoon's rulings (`../rulings.md`, Q1–Q11 and the Q7
follow-up of 2026-11-17).
- It proves four `sorry`'d targets:
  - T2 and T3 in `IdentityBased/BonehBoyenSecurity.lean`;
  - `ProbComp.expect_simulate_rel` and `ProbComp.expect_sample_rel` in `Games/Relational.lean` (#351).
- It inserts the **ten approved readers** verbatim as pure insertions: six in `IdentityBased/Defs.lean` and four in
  `IdentityBased/BonehBoyen.lean`.
- It reads the real setup through the probe's `RealReads`/`setup_out` interface.

Together with T4 (#346), the result makes `bb1_sidSecure` ([BB04, Theorem 4.1] at depth 1) standard. The bb1-sim gate
audits the readers and the fill (Q8; #351 and #352 go to DW-11).

**Bases** (Q9: stacked on T4's PR, which is open):
- **Issue base** `89a18a8225be1b76166af12a15179da291747783`, #346's head.
- **Patch base** `72c0498a77dd0aadf8cc2a2e71cb450d754f8f5c`, a deterministic unsigned merge of the records tip
  `ca129d64cd54a92aabe517e5262058664b49f651` into the issue base (tree `b5a5842dd0a5af86975864b29065bec44758f561`).
  - The tip is Lean-equal to `463f2244`, the #352 merge and olean snapshot #4.
  - The merge is needed because #346 predates #351 and #352: `Relational.lean` and the group helpers are not at the
    issue base.
- **Check base** `7cfe2b1b9a7e001d9ae972811cf85a332518111d`, the patch base merged with #340's head
  `916afc25c21f5e52b4b01958186ad55d2f615fd1` (tree `02b2d44a1ebafbfb26baf84ba84a07e4ba62a19d`).
  - #340 changes only `Pairing/Assumptions.lean`, a direct import of `BonehBoyenSecurity`, so it is in the fill's
    closure.
  - It adds no module to the order: the order is the same 193 modules with or without it.
- **Merges.** All of them are clean (rc 0). The check tree is the same for every merge order. `tools/mkbase.sh` builds
  both base commits and checks their trees.
- **Rebase.** If #346 merges mid-job, the worker rebases onto the tip, as the brief's *Rebase* says.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1, with an adaptation for
this job). Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory. The design note, the rulings,
the statement-phase reviews and policy are on the records branch at the records tip, and the brief lists their
SHA-256s. The probe sources are in the statement job's delivery on the exchange (`a3cb45f6`).

**Pack contents:**
- [Build order](order.txt): 193 TCSlib modules at the check base, in import order. It is a subsequence of the
  depth-first post-order of the 1,427 modules reachable from `TCSlib.lean` and the two `audits/*/Checks`, with imports
  in file order. It is the upstream closure of every module downstream of a changed module, with the root `TCSlib`
  excluded. New helper modules go before `BonehBoyenSecurity` (position 191).
- [Closures](closures.txt):
  - `CHANGED`: the 4 existing modules the job may change;
  - `DOWN`: 13 modules, root excluded; this is the sweep, plus the helpers;
  - `INFO-DELTA`: the 9 modules whose source differs between the tip and the check base.

  Neither `audits/*/Checks` is downstream of a changed module.
- [Mathlib roots](roots.txt): 94, the same set as T4's package.
- [Source hashes](SOURCE-SHA256SUMS) of the 193 files at the check base, read from the git objects of tree `02b2d44a…`.
- [Base admissions](base-sorries.txt): 22 declarations in 10 modules of the order, from a syntactic scan (comments and
  strings stripped, `sorry` tokens attributed to the enclosing declaration; the cleanup Stage 1 scanner). They include
  the four targets. T1 is proved by #340, and T4 by #346. The final must leave 18 in 8 modules.
- `readers/`: the ten readers, byte-identical to the statement job's probe delivery
  (`Defs-block.lean.txt` `d6f8faf1…`, `BonehBoyen-block.lean.txt` `967f2a30…`). Inserted after `Defs.lean:430` and
  `BonehBoyen.lean:412`, they give the ruled pins `97ecb6e0…` (563 lines) and `88454d6f…` (760 lines). The maintainer
  reproduced both.
- `tools/`: `mkbase.sh` (the two base commits), and `graph.py` and `pins.py` (how the pin files were made).
- `staging-probe/`: the maintainer's light Lean probe at the check base, with the readers inserted, on a hard-linked
  copy of snapshot #4.
  - 16/16 modules have rc 0 and 0 errors.
  - The targets and readers elaborate.
  - T1, T4 and the readers use the standard axioms.
  - `bb1_sidSecure` reaches exactly T2 and T3.
  - The snapshot rehashed 0/0/0. The copy was deleted.

  `PROVENANCE.txt` has the details.

Claude returns at least one checkpoint and the final only at `inbox/fills/bb1-sim/` on the exchange. It never pushes a
campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md`, which sits beside this file in
`briefs/pairings/fills/bb1-sim/issued-fill-r1/` and is not part of the pack.

**Size** (maintainer's assessment). About 1,000–1,700 Lean lines:
- the readers (131, verbatim);
- the two `Relational` bodies (10–30);
- 3–5 helper modules (900–1,500, of which step M is largely the probe's proved consumer, ported);
- the T2/T3 assembly with refreshed sketches (80–200).

The long steps are mechanical: the 193-module bootstrap, a 13-module sweep plus the helpers, and four-variant
canonical seals of 4 owners plus the helpers, with base seals and controls. All of it runs one Lean process at a time.
One job is right. The suggested split gives the lead `Relational`, the lazy handlers, T3 and the integration;
sub-agent A step M; and sub-agent B the real side and the bad-coin bound.

**Open point for Seyoon (raised with the staging; the package implements the first option).** The patch base form:
- (A) the deterministic local merge above;
- (B) a maintainer merge of the tip into #346's branch first, then issue on that head;
- (C) wait for #346 to merge and issue on the tip.

**Maintainer steps before dispatch:** commit this folder to the records, write that commit's full hash for
`<RECORDS-PIN>` in `dispatch.md`, and push the exchange commit named there. If it is replayed onto a newer exchange
tip, its hash changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
