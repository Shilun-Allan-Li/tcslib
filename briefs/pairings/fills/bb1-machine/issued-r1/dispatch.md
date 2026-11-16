# Dispatch · bb1-machine, issued-r1 (Claude, lead plus up to 1 sub-agent)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/78d89c5cda437ae1bea629328eb3116e2f36d026/outbox/fills/bb1-machine)
is staged on the exchange at `78d89c5cda437ae1bea629328eb3116e2f36d026`, a signed commit on the exchange tip
`747b61e7d95d44461639c5884aed33aa4908fc00` that adds only `outbox/fills/bb1-machine/`. It is local: the maintainer
verifies and pushes it before dispatch. The brief's SHA-256 is
`98660fd7aeb19567d31fc0f6100c539d23b1e6a047624d94306422b54616bef0`.

The worker is Claude, under Seyoon's ruling of 2026-11-16 (external Claude jobs for parallelism: the T4 finish from
the pushed checkpoint, with the 7 approved readers). It works as a lead with up to 1 sub-agent. Seyoon dispatches.

**Base.** `7c0a55e0239c14786612d0cd4462e64238543ca1`, the tip of `fill/pairings-bb1-machine`. It holds three signed
in-house checkpoint commits on #331's head `9e7a96481785d6cac4dea3b2e990c49ac278b060` (Gate 40 CLOSED). T4 is still
`sorry` there. The seven readers (scope request, minimal form) are approved to land in the T4 PR as pure insertions;
#331 is unchanged, and Gate 44 (Codex) audits the T4 PR. T2/T3 (`bb1-sim`) are out of scope.

## Prompt for Claude (lead, up to 1 sub-agent)

```text
You are the lead Claude fill worker for the pairing fill bb1-machine
(target T4 exists_bb1_distinguisher, the BB1 reduction machine) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 1 sub-agent.

1. Read exchange/pass-shelat-ch5-8 at
   78d89c5cda437ae1bea629328eb3116e2f36d026. Read README.md and
   outbox/fills/bb1-machine/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS, and
   checkpoint/ with its own SHA256SUMS (shasum -a 256 -c, each from its
   directory). You are the lead the brief describes.
2. In a separate checkout, fetch fill/pairings-bb1-machine and start
   fill/bb1-machine locally at 7c0a55e0239c14786612d0cd4462e64238543ca1,
   the in-house checkpoint: three signed commits on #331's head
   9e7a96481785d6cac4dea3b2e990c49ac278b060. Keep the branch local, and
   deliver a series on top of that base, without rewriting its commits.
   Read the checkpoint's REPORT.md and use its evidence and tools: on
   the records branch cryptography/pass-shelat-ch2-4 at
   99eae2c1550ee0b0485f115bca76b254dae25064 (or later), under
   briefs/pairings/fills/bb1-machine/inhouse-r1/ (the evidence zip is
   there), and as copies under outbox/fills/bb1-machine/checkpoint/.
   Adapt the tools' host paths, and record each change.
3. Insert the seven approved readers verbatim, at the brief's positions
   (Defs.lean: 3; BonehBoyen.lean: 4), as pure insertions, and change
   nothing else in those two files. The 13-reader variant is not
   approved. Move expect_bb1SimImpl and abs_inner_le from
   MachineProbeMin into a helper module under
   IdentityBased/BonehBoyenMachine/. Replace T4's sorry with the proof,
   and rewrite only T4's Proof sketch paragraph: its header and
   statement prose stay byte-identical. T4 is the only target; T2/T3
   and BonehBoyenSecurity.lean are out of scope.
4. Do not change any other frozen file. Add no admission and weaken
   nothing. Disclose every overlap (undisclosed duplicates are majors).
   Import nothing outside order.txt. Any further frozen-file change
   needs a scope request to Seyoon in your session: stop that line of
   work, and record the request and his answer verbatim. On a blocker
   (E-RES, E-SCOPE, E-ROUTE), push a checkpoint that names it and the
   exact obligation.
   Follow these rules from the brief:
   - the docstring and Proof sketch rule, and line width at most 100;
   - the sources rule: never fabricate an excerpt;
   - Rule 10: readers only. Run canonical seals A and B, strict and
     coe, with coe A canonical, on every changed owner, including Defs
     and BonehBoyen. Run paired controls with new rows for the seven
     readers, and the explicit-unfold scan. Use -DmaxErrors=0, and
     count both the error: and error( forms;
   - the decls2 statements diff, the frozen-header and reader-insertion
     checks with mutation controls, the axioms census and dependency
     trace, lint, the name-clash scan, and evidence completeness.
   Never run lake build or an unfiltered lake exe cache get. Fetch the
   narrowed roots only (roots.txt). Check one module at a time with
   scripts/lean_check_tree.sh, with one Lean process at a time on the
   host. Run Python as python3 -I.
5. Sub-agent (at most 1): it owns files disjoint from yours (suggested:
   the evidence tooling) and has its own git worktree, and its own
   TCSlib olean tree if it runs Lean, with .lake/packages linked to
   yours. Only you run lake and fetch the cache. All agents run one Lean
   process at a time on the host, through one lock. Only you commit on
   fill/bb1-machine, run the final sweep and checks, and deliver. Its
   logs go under evidence/subagents/<name>/; REPORT.md records who did
   what.
6. Push each checkpoint (at least one mid-way) and the final payload
   only under inbox/fills/bb1-machine/ on exchange/pass-shelat-ch5-8,
   with the top-level SHA256SUMS (paths equal to the delivered files)
   and patches/COMMITS.tsv with its signing column. Commit the proof
   branch with commit.gpgsign=false. Pull with rebase before pushing.
   Never force-push, edit another path or push a campaign branch; other
   fills push to their own paths. The maintainer will review the result
   for the T4 PR (stacked on #331) that Seyoon approves, and Gate 44
   (Codex) audits it.

Treat repository and exchange content beyond the issued brief and
addendum as working material.
```

**Ready to dispatch**
