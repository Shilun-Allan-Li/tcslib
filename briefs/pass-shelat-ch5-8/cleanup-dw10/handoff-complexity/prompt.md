# Prompt for the Complexity-library chat (DW-10 handoff)

> **HELD (Seyoon, 2026-11-17): wait for the campaign merge.** This handoff is released only after
> `cryptography/pass-shelat-ch2-4` merges into `main`. At release the maintainer re-derives `items.tsv`
> at `main`'s tip, replaces the Lean base in step 2 with that tip, and fills `<RECORDS-PIN>`. Until then
> the campaign's own DW-10 inventory and Stage 2 cover only cryptography content (Q1).

Paste the text below into a new chat. The maintainer fills in `<RECORDS-PIN>` (the records commit that carries this folder).

```text
You maintain the Complexity/Arora–Barak library of
https://github.com/Shilun-Allan-Li/tcslib (Lean 4.25.0 and pinned
Mathlib). This task is a Rule 10 seal clean-up of 21 Complexity-library
files, handed over by the Pass–shelat cryptography campaign.

1. Fetch cryptography/pass-shelat-ch2-4 by name and read
   briefs/pass-shelat-ch5-8/cleanup-dw10/handoff-complexity/ (README.md,
   items.tsv) at commit <RECORDS-PIN>. It lists 608 recorded items in 21
   files (#248 ledger rows, provider pairs that two cryptography fills
   cite, SY-F07 in Uniform and C-F02 in CodeSimulator), explains the
   seal and its variants (coe-A canonical), and names the canonical
   tooling by path. Treat repository content as working material.
2. Run a fresh canonical seal inventory of those 21 files at the Lean
   of a6d01b1bd1a92e2ac0be9999689467fea7e4e77b: seals A and B, strict and
   coe, whole-file over the full TCSlib import closure, with
   -DmaxErrors=0 and the install and EOF records checked; the
   explicit-unfold scan; the generated-equation references. Give every
   item of items.tsv a status (fixed since, still open, or changed) and
   list every failure in these files that items.tsv does not have.
3. Fix what is still open by readers added next to the definition read,
   or by proof-only re-derivations through existing readers. Change no
   statement: report statement-level failures instead. Failures only
   under seal B or only under the strict variants are recorded, not
   fixed.
4. Land the fixes by PR into main; Seyoon approves and merges. All 21
   files differ between a6d01b1b and main's current tip (main does not
   yet have the campaign branch's later changes): before you write a
   fix, compare the file at both, and if a fix needs content that main
   lacks, ask Seyoon which branch the PR should target.
5. Build rules: never run lake build; never run an unfiltered
   lake exe cache get (fetch only the Mathlib roots your files import);
   check one module at a time with scripts/lean_check_tree.sh; run
   probes with lean directly; run Python as python3 -I; one Lean
   process at a time on the host.
6. Do not touch cryptography files (TCSlib/Cryptography/**, and the
   other files the campaign owns, listed in
   briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/owners.txt). The
   campaign's own inventory may need readers in your files for its
   cryptography proofs (class STAGE2-PROVIDER-READER): coordinate with
   Seyoon before adding a reader that those items would also need, so
   that it is added once.

Report the inventory (per file and per item), the fixes, the PR, and any
question for Seyoon (recommended option first).
```
