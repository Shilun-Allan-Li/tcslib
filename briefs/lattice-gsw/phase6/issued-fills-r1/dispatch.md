# Dispatch · gsw-6a-fills, issued-fills-r1 (Claude, lead plus up to 3 sub-agents)

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/aef43623edd9c96ab6c5731b3e76df55e7b4162c/outbox/fills/gsw-6a-fills)
is staged on the exchange at `aef43623edd9c96ab6c5731b3e76df55e7b4162c`.
- One SSH-signed commit on the exchange tip `4f436b659e3cb0cd633d82cd68cf3d869ed6a449` that adds only
  `outbox/fills/gsw-6a-fills/` (21 files). It is the staging commit `b1d05809` (built on `2eb7fbdc`), replayed by the
  maintainer with `git cherry-pick -S` onto the moved tip. It is **pushed**, and its folder verifies 13/13 from a
  fresh `git archive`.
- Brief SHA-256: `eba5b9f5c7cce2eeebc8f5b43a5f44bad1c1d94409f7fd860e3f9a0f50c7bce4`.

The worker is Claude in the cloud (standing ruling: Claude for fills; overnight ruling of 2026-11-17: the 6a units not
filled in-house go to an external job), a lead with up to 3 sub-agents. Seyoon dispatches.

**Scope.** U4 `BarringtonConverse` (C17–C21), U5 `NC1` (C22–C25), U7 `NANDLayering` (N7–N13), U9 `CarrySave`
(F5–F6), U10 `Compare` (F7–F8), U11 `ModSum` (F9–F10): 41 targets in six files. In-house and excluded: U1, U2 (proved
as a draft on `fill/gsw-6a-u1-u2`), U3 (in progress there), U8 and U6 (in progress on `fill/gsw-6a-u8-u6`).

**Base.** `05999162b77c1f0fef64b07427e1a041a31b43d2` (tree `7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3`): #360's head
`3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032` merged into #359's head `73aedcdaaaffef7e69ab012d9b9195f150bae68d` (on #358
`a616adcac0760ab56b1b0a2a4869f4763843f9ab`), unsigned, with fixed identity, dates and message. The commit is not on
any remote; the pack's `tools/mkbase.sh`, or the brief's `git merge --no-ff` recipe, re-creates it and checks both
hashes. #358, #359 and #360 are unmerged drafts; Gate 45 may still change statements, and any such change is the
maintainer's to handle.

**Records pin.** `7cbd0c93cb053ab399aa40e9163a1229a1d99360`, the tip of `cryptography/pass-shelat-ch2-4` at staging:
every records input the brief names is at it, with the SHA-256 the brief gives. This folder is not in it yet (step 1).

**Before dispatch** (maintainer):
1. Commit `briefs/lattice-gsw/phase6/issued-fills-r1/` to the records branch (its files equal the pack's, which adds
   `inputs/`). The prompt pins the inputs at `7cbd0c93…`, which stays valid; nothing in the prompt changes.
2. Push the exchange commit (`git push origin stage/gsw-6a-fills-exchange:exchange/pass-shelat-ch5-8`). If it is
   replayed onto a newer exchange tip (it touches only its own path, so the replay is clean), put the pushed hash in
   the pack link, the staging lines and the prompt.

## Prompt for Claude (lead, up to 3 sub-agents)

```text
You are the lead Claude worker for the GSW phase-6a fill job
gsw-6a-fills (lattice campaign) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 3 sub-agents on disjoint files.

1. Read exchange/pass-shelat-ch5-8 at
   aef43623edd9c96ab6c5731b3e76df55e7b4162c. Read README.md and
   outbox/fills/gsw-6a-fills/README.md, brief.md,
   fill-environment-addendum.md, targets.txt and inputs/ (plan
   section r3, the rulings, the 6a statement reviews, the #360
   review). Verify the pack with SHA256SUMS and inputs/SHA256SUMS
   (shasum -a 256 -c, from each directory). You are the lead the
   brief describes. The records inputs the brief names are at commit
   7cbd0c93cb053ab399aa40e9163a1229a1d99360 of
   cryptography/pass-shelat-ch2-4.
2. In a separate clone, fetch by name cryptography/pass-shelat-ch2-4,
   land/gsw-6a-statements (#359, head
   73aedcdaaaffef7e69ab012d9b9195f150bae68d) and land/gsw-6a-readers
   (#360, head 3ea428fd8b99ffe33cdfb8dbe8068d0eb000d032); if a branch
   has moved, fetch refs/pull/359/head and refs/pull/360/head or the
   pinned commits. Run the pack's tools/mkbase.sh: it must print
   BASE 05999162b77c1f0fef64b07427e1a041a31b43d2 tree
   7d551d6f5278fb79febe1b4eeffb4ca4329dc1d3 (or make the same commit
   with the brief's git merge --no-ff recipe). Start fill/gsw-6a-fills
   at that base and stay on it; your patches are against it. #358,
   #359 and #360 are unmerged drafts and Gate 45 may still change a
   statement: that is the maintainer's to handle, not yours.
   - Prove the 41 targets of targets.txt in their six files, one
     owner each: U4 BarringtonConverse (C17-C21), U5 NC1 (C22-C25),
     U7 NANDLayering (N7-N13), U9 CarrySave (F5-F6), U10 Compare
     (F7-F8), U11 ModSum (F9-F10). U1, U2, U3, U6 and U8 are filled
     in-house: their files are frozen and you cite their sorry'd
     targets as frozen statements (proved-modulo). Never use the
     in-house branches.
   - Headers, statement prose and definitions stay frozen; only the
     proof bodies, private helpers, the targets' Proof sketch
     paragraphs and the brief's few docstring lines may change. No
     new module and no new public declaration. If a target looks
     false, do not change it: report a counterexample.
   Follow the binding rulings the brief lists (P6-Q1..Q19, 6a Q1-Q4:
   no TreeCircuit.rename, use reidx; the #360 readers; N12 in field
   form), policy.md and the standing rules: Rule 10 readers only (no
   definitional unfolding of another file's definitions; a missing
   reader is a scope request to Seyoon, never an unfold); Rule 10
   seals with coe-A canonical, PolyExpr.eval and the FinDist
   coercion are notation; duplication: search TCSlib and Mathlib
   before any helper, and an inline re-derivation of a Mathlib or
   TCSlib lemma is a major (Gate 48 G48-01, Gate 44 G44-01);
   attribution and proof sketches per policy; line width at most
   100; files at most 1000 lines; no @[simp]; no sorry, admit,
   native_decide or axiom; disclose every deviation. Never lake
   build and never an unfiltered lake exe cache get; fetch only the
   pack's Mathlib roots; compile each module with
   scripts/lean_check_tree.sh. As a cloud worker you may run a
   memory-sized pool of Lean processes (at most nproc, keeping about
   2 GB or 15% of memory free, in dependency order, never two
   processes on one module or output file; workflow.md section 4.1
   and the addendum). Run Python as python3 -I.
3. Run the brief's checks: the bootstrap (218 modules, 115 sorry
   declarations in 18 modules) and the sweep at the head (the 9
   DOWN modules); admissions (exactly 74 in 12 modules, no sorry in
   any owned file); decls2 0/0/0 against the base, the StmtDump and
   the frozen check with controls; axioms with a dependency trace
   (sorryAx only through the in-house units' frozen targets; none
   through layerNAND); Rule 10 seals A and B, strict and coe, of the
   six owners at head and base, liveness controls and the unfold
   scan; the frozen-file check; lint against 25 FAIL / 390 WARN over
   513 files; sizes; docstrings; the clash and shadow scans; the
   reuse and overlap disclosures; and the git am reproduction.
4. Sub-agents (at most 3): each owns files disjoint from the others',
   with its own git worktree and its own TCSlib olean tree, and
   .lake/packages linked to yours; only you run lake and fetch the
   cache. All agents share one Lean pool. Only you commit on
   fill/gsw-6a-fills (commit.gpgsign=false; each commit touches one
   owned file), run the final checks and deliver. Sub-agent logs go
   under evidence/subagents/<name>/; REPORT.md records who did what.
5. Deliver checkpoint 1 (the base reproduced, the bootstrap, at least
   two units proved with their checks, outlines and searches for the
   rest) and the final, only under inbox/fills/gsw-6a-fills/ on
   exchange/pass-shelat-ch5-8: REPORT.md naming the full head hash;
   patches/ (git format-patch <base>..fill/gsw-6a-fills, with
   COMMITS.tsv and its signing column); src/ with every owned file at
   that head (every checkpoint carries src/ of every file it claims
   compiles); evidence/ with its manifest; and the top-level
   SHA256SUMS (paths equal to the delivered files). Commit on the
   exchange with git -c commit.gpgsign=false, pull with
   git -c commit.gpgsign=false pull --rebase, and check that
   git cat-file -p HEAD | grep -c gpgsig prints 0 before each push;
   the maintainer expects unsigned commits. Never force-push, never
   edit another path and never push a campaign branch. The
   maintainer reviews the result and lands it unit by unit.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the two steps above:

**Ready to dispatch**
