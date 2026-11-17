# Dispatch · cleanup-stage1, issued-r1 (Claude, lead plus up to 2 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/d929cc21ec817b2518d57a7262e42744728f029a/outbox/fills/cleanup-stage1)
is staged on the exchange at `d929cc21ec817b2518d57a7262e42744728f029a` (local branch `stage/cleanup-stage1-exchange`,
an SSH-signed commit on the exchange tip `6a9b6e19f908bbcd666c0460fa5fea54f20c1e7b` that adds only
`outbox/fills/cleanup-stage1/`; **not yet pushed**, so the link resolves only after the push). Brief SHA-256
`56368c1317380e704dfbfc44e6891f198c8dddd4949a82e5df39b348a81268f1`. The worker is Claude (standing ruling: Claude for
fills and all other external jobs), a lead with up to 2 sub-agents on disjoint files. Seyoon dispatches.

**Base.** Issue base `daa6e173cdd94cad1475b9a96eca613bce53ba61`, the head of #347 (DW-5). Check base: the merge of the
records tip at issue `f99901fdc98f4c7703cf9485329600311a1ea655` into it, tree
`01cc6259480ccc9372181cd4d18d4511c87aa048` (clean). The records tip `8adee3e6ace3ec78171fc499b3d101a252534d55`
(Seyoon's Stage 1 rulings) has the same Lean sources as `f99901fdc…`.

**Rulings.** CS1-Q1 to CS1-Q12 are ruled (`cleanup-stages.md` § *Stage 1 rulings*, at `8adee3e6…`); the brief
implements them (Q2, Q8, Q9 changed against the staging's recommendations).

**Records pin.** `f7308a62c3569c400051e8fe7e25663a94f8db8e`: the records commit that carries this folder. The maintainer writes its full hash
here, and in the prompt below, after committing.

**Before dispatch** (maintainer):
1. Commit `briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/` to the records branch; put that commit's full hash for
   `f7308a62c3569c400051e8fe7e25663a94f8db8e` in the **Records pin** line and in the prompt.
2. Push the exchange commit. If it is replayed onto a newer exchange tip, put the pushed hash in the pack link, the
   staging line and the prompt.

## Prompt for Claude (lead, up to 2 sub-agents)

```text
You are the lead Claude worker for the Pass-shelat cleanup Stage 1 job
cleanup-stage1 (promotions, additive only) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 2 sub-agents, on disjoint files.

1. Read exchange/pass-shelat-ch5-8 at
   d929cc21ec817b2518d57a7262e42744728f029a. Read README.md and
   outbox/fills/cleanup-stage1/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS
   (shasum -a 256 -c, from its directory). You are the lead the brief
   describes. The records of this issue are at commit f7308a62c3569c400051e8fe7e25663a94f8db8e of
   cryptography/pass-shelat-ch2-4
   (briefs/pass-shelat-ch5-8/cleanup-stage1/issued-r1/, equal to the
   pack); the stage plan with Seyoon's Stage 1 rulings, the duplication
   ledger, the deferred-work register and DW-5's README and tools are
   there too.
2. In a separate clone, fetch cleanup/dw5-derand-readers and
   cryptography/pass-shelat-ch2-4 by name. Start the local branch
   cleanup/stage1-promotions at the issue base
   daa6e173cdd94cad1475b9a96eca613bce53ba61 (#347's head). Build and
   check only at the check tree: a local branch from the issue base
   with f99901fdc98f4c7703cf9485329600311a1ea655 (the records branch's
   last Lean state) merged in, whose tree must be
   01cc6259480ccc9372181cd4d18d4511c87aa048, with your commits on top.
   Keep every branch local and commit with commit.gpgsign=false.
   Write the targets S1-01 to S1-27 (S1-13 withdrawn; 69 declarations)
   exactly as the brief states them, each with a formula docstring, a
   tag or glue note, readers for definitions, and a proof: DW-9's three view lemmas in
   IterateFindHost.lean; the new Games/Tapes.lean and
   ZeroKnowledge/InteractionWords.lean with their facade lines; the
   shared machine helpers in ZeroKnowledge/EncodingMachines.lean; the
   insertions in the other homes of the brief's Scope table. Additive
   only: no existing declaration, proof, import or docstring changes,
   nothing is re-pointed or deleted (that is Stage 2). Do not edit the
   files the GSW/IBE jobs own (the brief lists them; the DL-40
   averaging bound is bb1-sim's, and mul_prob_le_expect is Stage 2's).
   Declare protected every new name whose short name already exists.
   Seyoon's rulings CS1-Q1 to CS1-Q12 are binding as the brief states
   them; do not decide a further open question yourself. Follow
   policy.md and the standing rules: readers only (Rule 10); line width
   at most 100; no @[simp]; never fabricate a citation. Use only narrowed Mathlib roots, never lake build and
   never an unfiltered lake exe cache get, and check one module at a
   time with scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Run the brief's checks: the 847-module bootstrap and the replay
   sweep of the 495 modules downstream of the changed files (root
   excluded) at the check head, with the merge-tree equality;
   admissions against base-sorries.txt (unchanged); decls2 against the
   issue base (ADDED exactly the targets, 0 CHANGED, 0 REMOVED) and a
   StmtDump with the header check; axioms (standard, no sorryAx); the
   insertion check with controls; Rule 10 canonical seals A and B,
   strict and coe, on every new or changed owner, base seals at the
   check base, paired controls on every changed owner, and the
   explicit-unfold scan; lint; sizes; the name-clash and shadow scans;
   and a reuse search for each target (an undisclosed duplicate of a
   public lemma is a major). If a statement does not elaborate, looks
   false, or misses a listed copy as an instance, do not weaken it
   silently: report it as a question for Seyoon.
4. Sub-agents (at most 2): each owns files disjoint from yours and from
   the other's (the brief suggests a split), with its own git worktree
   and its own TCSlib olean tree, and .lake/packages linked to yours;
   only you run lake and fetch the cache. One Lean process at a time on
   the host, for all agents, through one lock. Only you commit on
   cleanup/stage1-promotions, run the final checks and deliver.
   Sub-agent logs go under evidence/subagents/<name>/; REPORT.md
   records who did what.
5. Deliver checkpoint 1 (every target statement elaborating at the
   check tree, with decls2, the StmtDump, the shadow scan and the reuse
   table) as soon as it is ready, and the final, only under
   inbox/fills/cleanup-stage1/ on exchange/pass-shelat-ch5-8: REPORT.md
   with the Stage 2 re-point table; patches/ (git format-patch from the
   issue base) with COMMITS.tsv and its signing column; src/;
   evidence/ with its manifest; and the top-level SHA256SUMS (paths
   equal to the delivered files). Pull with rebase before pushing.
   Never force-push, never edit another path and never push a campaign
   branch. The maintainer will review the result for the Stage 1 PR,
   which Gate 47 audits together with #347.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the steps above:

**Ready to dispatch**
