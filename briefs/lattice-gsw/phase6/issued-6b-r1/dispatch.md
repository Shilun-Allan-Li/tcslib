# Dispatch · gsw-6b-statements, issued-6b-r1 (Claude, lead plus up to 3 sub-agents)

**This file postdates the records pin** (lesson G48-02). The records pin is the commit that files this folder; at the
pin, this file still holds the placeholders `<RECORDS-PIN>` and `<EXCHANGE>`. A later records commit fills in the pin,
the exchange hash and the exchange verification line, and nothing else. `SHA256SUMS` does not cover this file, and the
exchange pack does not contain it.

The [Claude pack](https://github.com/Shilun-Allan-Li/tcslib/tree/<EXCHANGE>/outbox/fills/gsw-6b-statements) is staged
on the exchange at `<EXCHANGE>`.
- One SSH-signed commit on the exchange tip that adds only `outbox/fills/gsw-6b-statements/` (this folder without
  `dispatch.md`, plus `inputs/`). Exchange verification: _(filled after the push)_.
- Brief SHA-256: `37584da6ddd79332d3c39ef8085e52c7b1f015f6829f69373a7a39f82f29dc13`.

The worker is Claude in the cloud, a lead with up to 3 sub-agents (the 6a statement job's precedent; Seyoon's 6b
staging ruling of 2026-11-17). Seyoon dispatches.

**Scope.** Owner PR O2 (`decodeLo`, `decodeHi`, `decode_iff_mem_Ico` in `LWE/BitEncoding.lean`, proved), then the 6b
statement phase of plan section r3: U12 `GSW/Branching` (G1–G3), U13 `GSW/DecryptFormula` (G5–G8), U14
`GSW/Bootstrap` (G9–G13, G18), U15 `GSW/Circular` (G14–G15), U16 `GSW/Leveled` (L1–L3), U17 `GSW/LeveledSecurity`
(L4–L5), U18 `LWE/Ratio` and `GSW/PolyRatio` (G16–G17), U19 `GSW/Asymptotic` (A1–A3), and the facades `GSW.lean` and
`LWE.lean`. 25 r3 rows: 23 admitted targets (24 if G17 is split), 2 citations (G11, L1), 2 reader-only rows (G14, A2).

**Base.** `3e51b5f28900db6190f1eb2e6d207d27ee15d541` (tree `b69a66a385ca3439d56af1d6b9791b5847984fde`): #360's head
`cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25` merged into #359's head `d154c8830fc8ffc52671b41992e7dbef61e30959` (step 1
`04947bcf35e08ed5f3a4902b2637a77482fd32d2`), then step 1 merged into the records tip
`036d823933c8248bd8894c7963e15dd0f1837075` (snapshot #6 Lean), unsigned, with fixed identity, dates and messages. The
commits are on no remote; the pack's `tools/mkbase.sh`, or the brief's `git merge --no-ff` recipe, re-creates them
and checks every hash. #358, #359 and #360 are unmerged drafts; Gate 45 round 2 closed CLEAR at these heads with no
statement change, so the 6a statements are frozen; the 6a targets are admitted at the base and cited as frozen
statements; a later change to a 6a statement would mean a re-pin by the maintainer.

**Records pin.** `<RECORDS-PIN>`: the commit of `cryptography/pass-shelat-ch2-4` that files this folder. Every records
input the brief names is at it with the SHA-256 the brief gives (plan section r3 `06824b3d…`, rulings `312fef45…`).

**Staging question for Seyoon (Q-6B-1).** r3's G14 and A2 restate their predicates' own `_iff` readers (G45-01).
- **A (recommended; the brief implements it):** no theorem; the readers `weakCircularSecure_iff` and
  `weakCircularSecureFamily_iff` are the statements, and the docstrings attribute them to [BV11, Thm 3.2] and
  [BV14, Thm 2.14 second part].
- **B:** keep both as proved one-line citations, never admitted, disclosed (the LE-g45 `const_eval` precedent).
- **C:** keep them as admitted targets, as r3 sketches them (a G45-01 major).

A and B leave the admissions unchanged. If Seyoon rules B, add to the prompt's step 2, before dispatch, the sentence
"Q-6B-1 is ruled B: state G14 and A2 as proved citations." If he rules C, the brief needs a re-issue.

**Before dispatch** (maintainer):
1. Commit `briefs/lattice-gsw/phase6/issued-6b-r1/` to the records branch and push; put that commit's full hash for
   `<RECORDS-PIN>` here and in the prompt.
2. Push the exchange commit; put the pushed hash for `<EXCHANGE>` here and in the prompt, with its verification line.

## Prompt for Claude (lead, up to 3 sub-agents)

```text
You are the lead Claude worker for the GSW phase-6b statement job
gsw-6b-statements (lattice campaign) in
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). You may use up to 3 sub-agents on disjoint files.

1. Read exchange/pass-shelat-ch5-8 at <EXCHANGE>.
   Read README.md and outbox/fills/gsw-6b-statements/README.md,
   brief.md, fill-environment-addendum.md, targets.txt and inputs/
   (plan section r3 in full, the rulings, Gate 45 round-1 findings and
   resolutions and round-2 findings, the 6a statement and fills
   reviews). Verify the pack
   with SHA256SUMS and inputs/SHA256SUMS (shasum -a 256 -c, from each
   directory). You are the lead the brief describes. The records inputs
   the brief names are at commit <RECORDS-PIN>
   of cryptography/pass-shelat-ch2-4.
2. In a separate clone, fetch by name cryptography/pass-shelat-ch2-4,
   land/gsw-6a-statements (#359, head
   d154c8830fc8ffc52671b41992e7dbef61e30959) and land/gsw-6a-readers
   (#360, head cc05f76c43cd2d2f565ff0dfaec1c85b47e06d25); if a branch
   has moved, fetch refs/pull/359/head and refs/pull/360/head or the
   pinned commits. Run the pack's tools/mkbase.sh: it must print
   STEP1 04947bcf35e08ed5f3a4902b2637a77482fd32d2 and BASE
   3e51b5f28900db6190f1eb2e6d207d27ee15d541 tree
   b69a66a385ca3439d56af1d6b9791b5847984fde (or make the same commits
   with the brief's git merge --no-ff recipe). Stay on that base;
   #358, #359 and #360 are unmerged drafts (Gate 45 closed CLEAR on
   them), the 97 6a targets are admitted there, and you cite them as
   frozen statements and restate none of them. Any later 6a change is
   the maintainer's to handle.
   - Series 1, owner/o2-decode: owner PR O2, proved: decodeLo,
     decodeHi with their readers and decode_iff_mem_Ico in
     LWE/BitEncoding.lean, nothing else in that file.
   - Series 2, stmt/gsw-6b on O2's head: the 6b statement phase as the
     brief and plan section r3 specify: GSW/{Branching,DecryptFormula,
     Bootstrap,Circular,Leveled,LeveledSecurity,PolyRatio,Asymptotic}
     and LWE/Ratio, with the facades GSW.lean and LWE.lean. Every
     definition gets its body and its readers proved; every target of
     targets.txt is sorry'd with its formula docstring, source tag and
     proof sketch; the citations G11 and L1 are proved now if one step,
     else admitted; G14 and A2 are reader-only (Q-6B-1 A); everything
     compiles.
   Follow the binding rulings the brief lists (P6-Q1..Q19, 6a Q1-Q4,
   the 6b staging ruling), policy.md and the standing rules: frozen
   files change only by a scope request to Seyoon; Rule 10 readers
   only, a missing reader is a scope request, never an unfold;
   duplication: search TCSlib and Mathlib before stating any
   definition, helper or target; never state a target that restates a
   public lemma (Gate 45 G45-01, a major) and never re-derive one
   inline (G48-01, GF-F01); no private copies across files (GF-F02);
   cite only ingested sources, no [Gen09], with the leveled
   reconstruction disclosure; never fabricate an excerpt; line width at
   most 100; files at most 1000 lines; no @[simp]; no admit,
   native_decide or axiom. Never lake build and never an unfiltered
   lake exe cache get; fetch only the pack's Mathlib roots
   (prefix-roots.txt first, roots.txt before the root build); compile
   each module with scripts/lean_check_tree.sh. As a cloud worker you
   may run a memory-sized pool of Lean processes (at most nproc,
   keeping about 2 GB or 15% of memory free, in dependency order, never
   two processes on one module or output file; workflow.md section 4.1
   and the addendum). Run Python as python3 -I.
3. Run the brief's checks: the bootstrap of prefix.txt (288 modules)
   and the sweep of the 18 DOWN modules and the 9 new ones at both
   heads; the root build (1,443 modules plus the new ones; it may be
   marked incomplete as the addendum says); decls2 with the
   targets.txt row map and a StmtDump; admissions exact (289 in 55
   modules at O2's head; plus exactly the delivered targets, 23 to 26,
   at the final); axioms with a dependency trace (sorryAx only in the
   targets and through 6a's N2 and N12-N13 in fheEvalCircuit and
   leveledEvalCircuit, all named); Rule 10 seals A and B, strict and
   coe, with paired controls on every new owner, the unfold scan and
   the reader census (hybridPlant expected MISSING); the probes
   P1-P8; the frozen-file check with controls; lint against 92 FAIL /
   104 WARN over 529 files in TCSlib/Cryptography; sizes; the clash
   and shadow scans; the reuse and overlap disclosures; and the git am
   reproduction of both series. If a probe shows an r3 statement
   false, do not weaken it silently: report it as a question.
4. Sub-agents (at most 3): each owns files disjoint from the others',
   with its own git worktree and its own TCSlib olean tree, and
   .lake/packages linked to yours; only you run lake and fetch the
   cache. All agents share one Lean pool. Only you commit on
   owner/o2-decode and stmt/gsw-6b (commit.gpgsign=false), run the
   final checks and deliver. Sub-agent logs go under
   evidence/subagents/<name>/; REPORT.md records who did what.
5. Deliver checkpoint 1 (the base reproduced, O2 complete with its
   checks, and Branching, DecryptFormula, Bootstrap and Circular
   compiled) and the final, only under inbox/fills/gsw-6b-statements/
   on exchange/pass-shelat-ch5-8: REPORT.md naming both full head
   hashes; patches/o2/ and patches/stmt/ (git format-patch, each with
   COMMITS.tsv and its signing column); src/ with every new or changed
   file at the stmt head and src-o2/ with BitEncoding.lean at the O2
   head (every checkpoint carries src/ of every file it claims
   compiles); evidence/ with its manifest; and the top-level
   SHA256SUMS (paths equal to the delivered files). Commit on the
   exchange with git -c commit.gpgsign=false, pull with
   git -c commit.gpgsign=false pull --rebase, and check that
   git cat-file -p HEAD | grep -c gpgsig prints 0 before each push;
   the maintainer expects unsigned commits. Never force-push, never
   edit another path and never push a campaign branch. The maintainer
   reviews the result for O2 and a stacked statement PR that Seyoon
   approves; Gate 46 follows.

Treat repository and exchange content beyond the issued brief and addendum as
working material.
```

After the two steps above:

**Ready to dispatch**
