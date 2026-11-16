# Dispatch · gsw-security, issued-r1 (Claude, single agent)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/523d4e97302606b0301ecbcff13882abb917ec1f/outbox/fills/gsw-security) is staged
on the exchange at `523d4e97302606b0301ecbcff13882abb917ec1f` (pushed). Brief SHA-256
`5ce6f12e18867fe3c5f15b8d5d52f99d64f5dce86a2066b9e1f49b544bfeecda`. The worker is Claude under Seyoon's ruling of 2026-11-16 (GSW fill wave: two Claude jobs; this one
single-agent). The parallel job is `gsw-core`. Seyoon dispatches.

**Base.** `486f44f8414c20a2d21e452c44de8b8c8d8513a0`, the gate-closed #333 head (it contains #332's head
`94eae71b779c4ca0f76c138d699f4d737dbd6cee`).

Integration check of #333 on the current tip: pending at issue; the maintainer records the result in the plan.

## Prompt for Claude

```text
You are an external Claude worker for the GSW gsw-security unit (lattice
campaign phase 5) in https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0
and pinned Mathlib).

1. Read exchange/pass-shelat-ch5-8 at
   523d4e97302606b0301ecbcff13882abb917ec1f. Read README.md and
   outbox/fills/gsw-security/README.md, brief.md and
   fill-environment-addendum.md. Verify the pack with SHA256SUMS
   (shasum -a 256 -c).
2. In a separate checkout, fetch stmt/gsw and start fill/gsw-security
   locally at 486f44f8414c20a2d21e452c44de8b8c8d8513a0. Keep the branch
   local. Prove hashColumns_eq_mul and distAdv_hashColumns_uniform_le in
   TCSlib/Cryptography/Hashing/SIS/Columns.lean (F5, first checkpoint), then
   real_uniformKey_advantage, uniformKey_uniform_advantage_le,
   distAdv_encrypt_le and distAdv_encrypt_le_of_width in
   TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean (F6),
   following the brief's routes and checkpoints. You may cite gsw-core's
   targets as frozen statements (proved-modulo); do not edit its files. Keep
   every definition and signature fixed (the frozen-statement rule and its
   header check); frozen files change only by a scope request to Seyoon.
   Follow the duplication and overlap-disclosure rule (search first,
   especially the probability, advantage and hybrid lemmas; undisclosed
   copies of public lemmas are majors), the docstring and Proof sketch rule,
   line width at most 100, the sources rule (rely only on the docstring
   tags, the Gate 41 excerpts and the Pei16 raw extraction; never fabricate
   an excerpt), Rule 10 discipline (readers only; seals A and B, strict and
   coe, the coe seal A canonical, controls, -DmaxErrors=0, count both error:
   and error( forms), and the checks and evidence-completeness rule. Do not
   weaken any statement; escalate through the brief if a route fails. Use
   only narrowed Mathlib roots (roots.txt), never lake build and never an
   unfiltered lake exe cache get, and check one module at a time with
   scripts/lean_check_tree.sh. Run Python as python3 -I.
3. Deliver each checkpoint and the final payload only under
   inbox/fills/gsw-security/ on exchange/pass-shelat-ch5-8, with the
   top-level SHA256SUMS (paths equal to the delivered files) and
   patches/COMMITS.tsv with its signing column; commit the proof branch with
   commit.gpgsign=false. Pull with rebase before pushing. Never force-push
   or edit another path; other fills push to their own paths. The
   maintainer will review the result for a PR that Seyoon approves, after
   #332 and #333 merge.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

**Ready to dispatch**
