# Claude job `dw10-seal-inventory` (Pass–shelat DW-10: the historical seal-debt inventory, checks only)

Claude is the worker, a lead with up to 2 sub-agents on disjoint owner sets (standing ruling: Claude for fills and all
other external jobs). The job is DW-10 of the deferred-work register. Seyoon ruled on 2026-11-17: "inventory now, fix
in Stage 2" (`cleanup-stages.md` § *Historical seal debt*). It runs a fresh Rule 10 canonical-seal inventory of every
Pass–shelat-owned Lean file at the base, reconciles it with the recorded seal debt and classifies every open item by its
likely fix. **It changes no Lean source and opens no PR**: its `inventory.tsv` and `REPORT.md` are the input of the
cleanup Stage 2 brief and of Seyoon's separate rulings.

**Base.** Issue base `f472accd5e000a53d0fbe02b5414435429ce4a70`, the records tip at staging. Its Lean equals
`a6d01b1bd1a92e2ac0be9999689467fea7e4e77b`, the merge of #341 (`git diff` over `TCSlib`, `TCSlib.lean`, `audits`, the
lakefile, the manifest and the toolchain is empty; `TCSlib` tree `06b51ea90a9a0ef49e1dc3e7034ba32ec9b75fe6` at both).
Not in the base: #347 (DW-5, open), which clears `IterateFind`'s 20 F-01 failures, and the running cleanup Stage 1
(additive promotions). The inventory records both as `pending` where they apply.

**Scope.**
- **434 owners** (`owners.txt`): 414 created by the campaign (T1) and 20 adopted by it (T2: Garg concrete-layer and
  InformationTheory files the campaign changed). Seals A and B, strict and coe; paired controls; the explicit-unfold
  scan. 24 facades are listed and not sealed.
- **21 list-only files** (`list-only.txt`): outside the campaign, but holding a reconciled item (`CodeSimulator`,
  `CircuitComplexity/Uniform` and 19 Arora–Barak/Complexity-library files with #248 rows or provider pairs). Seals and
  scan, no controls, never in the Stage 2 fix list.
- GSW, pairings and IBE, the lattice LWE/SIS layer, Arora–Barak and Ladner files are excluded; 18 further files the
  campaign touched but that hold no item are listed as considered and excluded.
- **Items to reconcile:** the #248 ledger's 764 historical observations and 813 current observations, the 72 + 52
  provider pairs of the 2026-11-10 rulings, and SG-F07, SY-F07 and C-F02 (78 rows). Each gets FIXED_SINCE, STILL_OPEN
  or CHANGED; every unrecorded failure is listed as NEW; every open item is classed STAGE2, SEAL-B-ONLY, STRICT-ONLY,
  STATEMENT or OUTSIDE.

Read [the brief](brief.md) and the [environment addendum](fill-environment-addendum.md) (v1 with an adaptation for this
job). Verify the package with `shasum -a 256 -c SHA256SUMS` from this directory.

- [Owners](owners.txt) with the derivation in its header, and [the list-only files](list-only.txt).
- [Build order](order.txt): 613 TCSlib modules at the base, the upstream closure of every owner and list-only file
  (root excluded), in the depth-first post-order of the 1,419 modules reachable from `TCSlib.lean`, imports in file
  order. [Closures](closures.txt): each target's positions, closure size and estimated requests.
- [Mathlib roots](roots.txt): 119, the Mathlib modules the 613 modules import directly (plus core `Std.Sat.CNF`).
- [Source hashes](SOURCE-SHA256SUMS) of the 613 files at the base, read from git objects.
- [Base admissions](base-sorries.txt): 22 declarations in 9 modules of the order, from a syntactic scan (comments and
  strings stripped, `sorry` tokens attributed to the enclosing declaration; it reproduces cleanup Stage 1's 26 on its
  order).
- The inputs: [ledger-historical.tsv](ledger-historical.tsv), [ledger-current.tsv](ledger-current.tsv),
  [provider-pairs.tsv](provider-pairs.tsv), [named-findings.tsv](named-findings.tsv). [derivation/](derivation/) holds
  the static tools that produced every list here, and `origins.tsv`.

Claude returns at least one checkpoint and the final only at `inbox/audits/dw10-seal-inventory/` on the exchange; it
never pushes a campaign branch. Seyoon dispatches with the prompt in the records' `dispatch.md` (beside this file in
`briefs/pass-shelat-ch5-8/cleanup-dw10/issued-r1/`; it is not part of the pack).

**Size** (maintainer's assessment). 455 sealed files, 1,820 seal probes before variant deduplication; at least 317,051
requests per variant for the owners by static count, about 520,000–630,000 by the recorded ratio; 160,044 owner lines
and 18,849 list-only lines. Serial Lean time roughly 12–18 h: bootstrap 1.5–2 h, seals 8–14 h, controls, collectors
and scans 1–2 h. One job is right, with a checkpoint once every file that holds an input item is sealed and scanned.
The suggested split gives the lead Complexity, InformationTheory, LearningTheory, the ch. 2–4 core and the list-only
files, sub-agent A SecureComputation, ZeroKnowledge and Composability, and sub-agent B Encryption, Authentication,
Games, Hashing, Randomness, Implications and Pseudorandom.

**Maintainer steps before dispatch:** commit this folder to the records, write that commit's full hash for
`<RECORDS-PIN>` in `dispatch.md`, and push the exchange commit named there. If it is replayed onto a newer exchange
tip, its hash changes: put the pushed hash in `dispatch.md` (and its parent) before dispatching.

**Ready to dispatch**
