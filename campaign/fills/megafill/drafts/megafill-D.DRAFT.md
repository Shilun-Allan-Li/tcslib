<!-- ISSUED (2026-10-27) as `campaign/fills/megafill/briefs/megafill-D.md`; this draft is kept as the record. -->
<!-- DRAFT (maintainer, 2026-10-26). Fill at issue: every ⟨…⟩ from the E-Q pre-ship at the issue
commit (@ANCESTOR@); then remove this comment. -->

# Megafill D: E-Q, the stage query in linear time

**One session, one host, a queue of one fill brief**, worked under Part 3 of the fill-agent
environment addendum (`campaign/standards/fill-environment-addendum.md`, **v2.5**). The item is its
own fill: its brief binds it, and it has its own branch, checks, screens, `REPORT.md` and zip,
exactly as if it had been dispatched alone. **The agent is Codex.**

## Repository and the shared base

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it fails, **stop**.
  That commit, **the shared base**, contains:
  - this cover brief and the item brief `campaign/fills/eq/briefs/eq-fill-query.md`;
  - its inputs, order list, base sorry set, screen base and pre-ship log;
  - **its prerequisites:**
    - A1's readings of the chapter predicates (PR #164), among them
      `Complexity.timeConstructible_iff`;
    - the sequence form of round iteration, `Turing.Round.iterate_seq` (PR #167);
  - the route's design note `campaign/items/c1/c1e/EQ-route-design.md`, and the brief's review
    (`campaign/fills/eq/reviews/brief/REVIEW.md`);
  - the addendum v2.5.
- Every attached brief must match its repository copy at that commit except for its
  `@ANCESTOR@` placeholders, and its SHA-256 must be the one the dispatch message gives.

## Once, at the start

1. **Part 1 of the addendum:** the preflight (item 1, with its floors: 12 GiB free on the clone's
   filesystem, 4 GiB of memory headroom as the addendum computes it), the toolchain, one clone.
   If Lean cannot start, Part 2 applies. **If Lean never runs, deliver the environment report
   only: do not draft proofs blind.**
2. **The cache** (Part 3, item 2): log the cache tool's archive store first, then fetch for the
   item's order list's Mathlib roots: **⟨N⟩ roots** (⟨N⟩ modules). Never the unfiltered
   `lake exe cache get`, never `lake build`.
3. **Keep the shared logs** under `evidence/logs/` at the clone's root (preflight, cache store,
   roots, cache fetch, manifest and cache checks), and **copy them into the item's zip**.

## The queue

| # | Item | Brief | Branch | Zip | Budget |
|---|---|---|---|---|---|
| 1 | E-Q: `Turing.NTimeDiag.exists_queryTM` (`Diagonalization/NTimeDiagonalizer`) | `eq/briefs/eq-fill-query.md` | `fill/eq-query` | `fill-eq-query.zip` | the session |

The budget is wall-clock from the branch's creation (Part 3, item 3.4). The screen takes about
⟨N⟩ minutes a run at the base on the maintainer's host (peak memory ⟨N⟩ GB). Never switch
branches while a screen runs.

## The item (Part 3, item 3)

1. Start from a clean tree: `git checkout -b fill/eq-query <the shared base>`.
2. **Its first edit:** its overlay (eight imports).
3. **Re-bootstrap its whole order list** (`campaign/fills/eq/orders/eq-fill-query.txt`, ⟨N⟩
   modules). Log each module's start and end time and **its maximum memory**, and the whole as
   the item's bootstrap.
4. Do the item as its brief says, through its delivery zip, and **deliver that zip at once**.
5. **One checkpoint, one commit, one zip.** After each of the brief's seven checkpoints, commit
   and write `fill-eq-query-cp<N>.zip`, and deliver it as soon as it is written. The session may
   end at any time, and a finished checkpoint must survive it. Megafill C's grouped checkpoint
   zips (its item's E-CHK) were a disclosed process deviation; do not repeat it.
6. **Budget** (Part 3, item 3.4): when the session must end, finish the step in progress, commit,
   and write the item's partial zip with its `REPORT.md`: the checkpoints reached, every open
   declaration with its literal "Proof sketch", and the axiom walk. A partial is the likely
   outcome of one session (2,400–3,900 lines, an ESTIMATE), and it is fine.
7. **Escalations** follow the brief's ground rules. If nothing is left that its escalations allow,
   the item ends early, with its zip.

## Environment rules for the session (addendum v2.5, with megafills A and C's lessons)

- **Part 1 applies on this host** and **Part 3** governs the session: one preflight, one cache,
  `df -B1` of the clone recorded before the item (E-RES below 3 GiB free stops the session).
- **One Lean process at a time** and **one screen at a time**, under `nice -n 10`. Every check
  through `scripts/lean_check_tree.sh`.
- **After a proof edit, re-check the order list's tail from the edited module on**, not the
  module alone.
- **The shared environment logs go in the item's zip**, and **memory is logged per module** (in
  the bootstrap, the final sweep and every probe).
- **A seal not run is a checklist failure**, and so is a seal without `rfl` controls that fail
  sealed and close unsealed (the brief's ground rule 10). Ship the raw outputs. A reducible
  `abbrev` (such as `Turing.Cfg.Halted`) cannot be sealed under Lean's default reducibility
  check; reading it through its body is allowed (`policy.md`).
- **The import probe covers every external name the source cites**: the proof-term walk and the
  source-level tactic arguments (megafill C's gate, round 2).

## Delivery

- The item's zip (and its checkpoint zips) **as soon as it is written**, named as its brief says.
- At the end, or when the session must stop, `megafill-d-REPORT.md` (Part 3, item 6): the item's
  outcome (complete; partial, with its checkpoints; or not started) with its branch's start and
  end times and its zip's SHA-256; the preflight and cache numbers.
