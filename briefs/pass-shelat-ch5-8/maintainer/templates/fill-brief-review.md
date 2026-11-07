# Fill-brief review (common part)

You review ONE fill brief before it is issued to an external fill worker (a Claude/Codex session that
only sees the brief, the environment addendum and the repository). Your verdict is "issue as is",
"issue after edits" or "do not issue", with a suggested diff. You do not edit the brief yourself and
do not commit or push. `SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`.

## Delivery model — refresh before using this historical template

The maintainer must ask the user Codex or Claude before preparing the fill and record the answer.
Check that the issued brief and prompt use that route: Codex returns Markdown/ZIP in chat and
cannot push; Claude may push only its own exchange delivery path. Campaign landing changes go
through a user-approved PR; D-0 still permits direct maintainer record pushes.

## Context
- The brief will be issued on `cryptography/pass-shelat-ch2-4` once PR #210 (the equation-lemma PR,
  head `fff0430c7c9db136e60ed14b069e972c2ea56fc8`, branch `wip/eqlemmas`, worktree `$SP/wt-e1`) merges.
  So **check the brief against #210's head**, not the base: its prerequisite tables should now be
  satisfied by #210's lemmas (list: `/home/user/tcslib/briefs/pass-shelat-ch5-8/gates/07-eqlemmas/evidence/decls.tsv`,
  worker reports in `…/07-eqlemmas/worker-reports/`).
- Standards: `/home/user/tcslib/policy.md` (rule 10, docstrings, proof sketches, reuse-not-copy),
  `/home/user/tcslib/briefs/pass-shelat-ch5-8/fills/fill-environment-addendum.md`,
  `/home/user/tcslib/briefs/pass-shelat-ch5-8/EXCHANGE.md` (delivery protocol), and
  `/home/user/tcslib/briefs/pass-shelat-ch5-8/mathlib-overlap-nt.md` (Mathlib-first for number theory).
- User rulings that the brief must respect (2026-11-06): fills run in parallel on separate hosts;
  zero exclusions (no proof reads another file's definition; type-valued fields through the published
  `…_domEquiv`); `BlumDensity` stays a hypothesis; size exceptions for `Candidates/RSA.lean`,
  `Candidates/Rabin.lean`, `Asymptotic/Collections.lean`; shared factoring statements S1–S3 exist (sorried)
  in #210.

## What to check
1. **Every Lean name the brief cites exists at #210's head** with the cited meaning: write a probe
   `$SP/wt-e1/Probe/Review<Unit>.lean` importing the owned modules and `#check @Name` each; run it with
   `cd $SP/wt-e1 && PATH="$HOME/.elan/bin:$PATH" TCSLIB_OLEANS=$SP/e1-oleans bash scripts/lean_check_tree.sh Probe/Review<Unit>`
   (one Lean process at a time; never `lake build`, never `lake exe cache get`; if a module is stale,
   re-check it first with the same script). Keep the log under `$SP/review/<brief>/`.
2. **The prerequisite tables** are now met by #210 (name each lemma), or say what is still missing.
   Remove "Before issue" conditions that are now satisfied; flag any that are not.
3. **Targets:** the units' target lists equal the `sorry`s in the owned files at #210's head (including
   restated targets, e.g. `fullDLCollection_hardCore`); statements quoted in the brief match the source.
4. **Routes:** each prescribed route is plausible and consistent with rule 10 (it names published lemmas,
   never unfolds a foreign definition); the Mathlib names to cite are right; nothing asks a worker to
   prove what Mathlib or TCSlib already has.
5. **Self-containment and protocol:** a worker with only the brief, the addendum and the repository can
   start: repository/branch, `@ANCESTOR@` placeholder, order lists/roots paths (regenerate counts with
   `$SP/ab-ref/fillinputs.py /home/user/tcslib fff0430c7c9db136e60ed14b069e972c2ea56fc8 <module> <outdir>`
   — it reads git objects, so the hash works — and say if they changed), delivery via
   `inbox/fills/<unit>/` on the exchange branch, checkpoints, REPORT checklist, escalation rules,
   statement freeze, budget order. Codex requires a complete chat Markdown/ZIP payload and no
   push instruction; Claude uses its assigned exchange path. Missing model selection or
   contradictory transport instructions must be fixed before issue.
6. **Parallel safety:** units own disjoint files; no unit needs another unit's unfinished proof (only
   statements); authorized imports create no cycles.
7. **Clarity:** plain, unambiguous English; flag anything a worker could misread.

## Output
Write `/home/user/tcslib/briefs/pass-shelat-ch5-8/fills/<brief>/review.md`: verdict line, then
numbered findings (severity blocker/major/minor), each with the exact suggested replacement text, then
the probe results. Report back the verdict and the blocker/major findings in a few lines.
