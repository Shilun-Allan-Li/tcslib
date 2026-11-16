# Dispatch · gsw-core, issued-r1 (Claude, lead plus up to 2 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/665b89fdf162077076d3b9cde0ff6855e5c84ffa/outbox/fills/gsw-core) is staged on
the exchange at `665b89fdf162077076d3b9cde0ff6855e5c84ffa` (local commit, for the maintainer to verify and push). Brief SHA-256
`c1a603cc26613cd9399248727aee2a90cef192065a17fd07572bc1c7534c4483`. The worker is Claude under Seyoon's ruling of 2026-11-16 (GSW fill wave: two Claude jobs; this one
multi-agent, up to 2 sub-agents). The parallel job is `gsw-security`. Seyoon dispatches.

**Base.** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the gate-closed #333 head. It contains #332's head
`94eae71b779c4ca0f76c138d699f4d737dbd6cee`, so F0's `getD_lt_depth` and `runWith_rel` are proved in the base.

Integration check of #333 on the current tip: pending at issue; the maintainer records the result in the plan.

## Prompt for Claude (lead plus up to 2 sub-agents)

```text
You are the lead Claude fill worker for the GSW gsw-core unit (lattice
campaign phase 5) in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0
and pinned Mathlib). You may use up to 2 sub-agents.

1. Read exchange/pass-shelat-ch5-8 at
   665b89fdf162077076d3b9cde0ff6855e5c84ffa. Read README.md and
   outbox/fills/gsw-core/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS
   (shasum -a 256 -c). You are the lead the brief describes.
2. In a separate checkout, fetch stmt/gsw and start fill/gsw-core locally at
   486f44f8414c20a2d21e452c44de8b8c8d8513a0. Keep the branch local. Prove
   the 29 targets of TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/
   Gadget.lean, Noise.lean, Scheme.lean, Symmetric.lean and Eval.lean (plan
   units F1, F2, F3, F7, F4), following the brief's routes, dependency order
   (F1, F2, then F3 and F7, then F4; proved-modulo the frozen statements of
   earlier units) and checkpoints (at least one mid-way). F0's
   DAGGate.getD_lt_depth and runWith_rel are proved in the base: use them.
   Keep every definition and signature fixed (the frozen-statement rule and
   its header check); frozen files change only by a scope request to
   Seyoon. Do not edit Columns.lean or Security.lean: the parallel job
   gsw-security owns them. Follow the duplication and overlap-disclosure
   rule (search first; undisclosed copies of public lemmas are majors), the
   docstring and Proof sketch rule, line width at most 100, the sources rule
   (rely only on the docstring tags, the Gate 41 excerpts and the Pei16 raw
   extraction; never fabricate an excerpt), Rule 10 discipline (readers
   only; seals A and B, strict and coe, the coe seal A canonical, controls,
   -DmaxErrors=0, count both error: and error( forms), and the checks and
   evidence-completeness rule. Do not weaken any statement; escalate
   through the brief if a route fails. Use only narrowed Mathlib roots
   (roots.txt), never lake build and never an unfiltered lake exe cache
   get, and check one module at a time with scripts/lean_check_tree.sh.
   Run Python as python3 -I.
3. Sub-agents (at most 2): each owns a disjoint set of target files, has its
   own git worktree and its own TCSlib olean tree, with .lake/packages
   linked to yours; only you run lake and fetch the cache. One Lean process
   at a time on the host, for all agents together, through one lock. Only
   you commit on fill/gsw-core, run the final sweep and checks, and
   deliver. Sub-agent logs go under evidence/subagents/<name>/; REPORT.md
   records who proved what.
4. Deliver each checkpoint and the final payload only under
   inbox/fills/gsw-core/ on exchange/pass-shelat-ch5-8, with the top-level
   SHA256SUMS (paths equal to the delivered files) and patches/COMMITS.tsv
   with its signing column; commit the proof branch with
   commit.gpgsign=false. Pull with rebase before pushing. Never force-push
   or edit another path; other fills push to their own paths. The
   maintainer will review the result for a PR that Seyoon approves, after
   #332 and #333 merge.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
