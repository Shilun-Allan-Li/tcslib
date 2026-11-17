# Arora–Barak chapters 3–4: closeout plan (draft for Seyoon's review, 2026-11-16)

Status: **rulings in progress (Seyoon, 2026-11-16).** Ruled: D1 = (a) remove; D2 = Exercise 3.6
covered by Ladner; D3 = the relativized hierarchies in scope (Exercise 3.3 brought in, then deferred again), the rest deferred;
D4 = refactor before integration, all three debt groups; D5 and D6 as proposed. All decided. **Go-ahead (Seyoon, 2026-11-16): run the queue.** The work
packages start once the decisions they depend on are ruled.

## 1. Where the campaign stands

Measured on the campaign after #325 (`20394834`, snapshot `oleans-c2039`) with the 2026-11-08
roadmap probes, rerun unchanged except for adding `Complexity.ladner`
(`campaign/status/2026-11-16-closeout-probes/`):

- **Headlines:** all 27 tracked headline theorems (9 for chapter 3, 17 for chapter 4, and
  `Complexity.ladner`) reach no `sorry` and print exactly `propext`, `Classical.choice`,
  `Quot.sound`. The 19 additional roadmap results print standard axioms only.
- **Admissions in the chapter scope** (the 145 modules under `ClassOracle`, `ClassPSPACE`,
  `Diagonalization`, `SpaceComplexity`, `TimeHierarchy`; 21,899 owned constants checked): exactly
  **21** direct admissions, all in `Complexity.ConfigCodec` (`ClassPSPACE/TQBF.lean`). The
  supporting kit `FormulaKit` (`Gate`, `Emit`) has **20** more. These 41 are the held RD-2/H6
  route (backlog §2 RD-2). No headline reaches them: TQBF's membership, hardness and
  completeness are proved through the ARM route.
- **Ladner** (P3.4) is complete: `Diagonalization/Ladner.lean` has no admission.
- **`main`**: the campaign is 1,016 commits ahead of their common base `abd2bd3d` (#179, 2026-10-28),
  and `main` is 25 ahead. `main`'s 25 change only GaussianSpace, PAC learning, information theory,
  cryptography, the blueprint and a dataset; **no TCSlib file changed on both sides**. The 41
  RD-2/H6 admissions are already on `main` (they came with #180), so integrating adds none. The
  other admissions under `Complexity` (`RAMSimulation` 14, `TuringMachine/Build/RecordTable` 4,
  `Expanders/Chernoff` 1) are inherited from `main` unchanged and are outside this campaign.
- **Blueprint:** the campaign has touched only 2 blueprint files; the chapters 3–4 increment has
  not been made. `main` reorganized the blueprint after the common base.

## 2. Decisions for Seyoon

**D1 · The RD-2/H6 route (41 admissions).** **Ruled (Seyoon, 2026-11-16): (a) remove.** A consumer
check on the campaign, `main` and the other remote branches found no use outside the route itself
(three docstrings mention it and are updated with the removal). `ConfigCodec` and `FormulaKit` have no consumer since
the ARM route proved TQBF (backlog §2 RD-2: "Fills held (user, 2026-10-14)"). Options:
- **(a) Remove** `ConfigCodec`'s admitted declarations and the `FormulaKit` modules, keeping
  `exists_adjacency_codec_cnf` (Claim 4.4(2), proved, standard axioms) and anything else proved
  that a consumer uses. One maintainer PR and gate. Recommended: it is the only option that makes
  the chapter scope admission-free without new fills, and removing an unused admitted API loses
  no proved result. Check first that no colleague branch consumes them.
- **(b) Fill them** (RD-2a semantics, RD-2b uniformity). The briefs were drafted on 2026-10-14
  against a pre-ARM `TQBF.lean`, so they would be regenerated; two or more Codex fills plus gates.
- **(c) Carry them** as a documented hold into `main` (they are already there). The chapters are
  then "done except a held, unused alternative route".

**D2 · Exercise 3.6 (a)(b).** **Answered (Seyoon, 2026-11-16, from the 2009 text):** (a) `H` is
computable in polynomial time, proved as `ladnerH_polyTime`; (b) if `SAT_H` is NP-complete, then
SAT is in P. **Ruled (Seyoon, 2026-11-16): no separate theorem**; it is Ladner in substance (under
`P ≠ NP` it is the third conjunct of `SAT_H_intermediate`). The four-line unconditional derivation
from targets 4 and 5 is archived as a probe (`probes/Ex36b.lean.txt`, standard axioms). Original
question: The plan lists Ladner's "Claim and Ex 3.6(a)(b)". The source check
(`campaign/items/ladner/2026-11-08-source-check.md`) could not verify the 2009 wording of those
parts, and the Lean cites Theorem 3.3 and its proof (PLAN §(f) fallback). The Claim is covered by
targets 3 and 4 (`ladnerH_bounded_of_mem_P`, `ladnerH_unbounded_of_not_mem_P`). Options: check the
2009 text yourself and either confirm coverage or add the parts as deferred; or close on the
fallback citation as recorded.

**D3 · The deferred items.** **Ruled (Seyoon, 2026-11-16):** bring two into scope before
closing: **Exercise 3.3** (a language `B ∈ EXP` with `P^B ≠ NP^B`; the existing
`exists_oracle_ne` gives `P^B ≠ NP^B` for a classically chosen `B` with no EXP bound), and the
**relativized hierarchy theorems**, by generalizing the existing hierarchy proofs rather than
duplicating them. Everything else listed below stays deferred. **Both later deferred again (Seyoon, 2026-11-16):** Exercise 3.3 (W8), and the relativized hierarchies (W9) until after the other closeout work, possibly after integration. Confirm that closeout leaves these deferred (plan §1, backlog §3):
- Chapter 3: Ex 3.1, 3.3, 3.4, 3.7–3.9; the relativized hierarchy statements; Remark 3.8 and
  §3.4.1 (expository);
- Chapter 4: Def 4.19 (read-once certificates; Thm 4.20 is proved directly on NDTMs) and
  Ex 4.7 (a certificate head moving both ways; added after gate 158, G158-07, from the scope
  plan's deferral, distinct from the proved Example 4.7); Example 4.15; Ex 4.2, 4.4–4.6, 4.8, 4.9,
  4.12;
- the queued additive NL closure lemma (P4.4) and the B5a linear-headline H2.

**D4 · Duplication debt at closeout.** **Ruled (Seyoon, 2026-11-16): refactor before integration,
all three groups**: the chapter 3–4 families (CH34-D2, D3, D4 leftovers, SG1-UH, FE-LIVE-1), the
12.2c infrastructure families (Catalog D-R2, the §12 sibling rows, Loop/RB4, ch7), and the ARM
layer (ARM-1/ARM-2). **Seyoon, 2026-11-16:** Hydroxyi no longer works on the ARM layer, so it
needs no coordination; the maintainer designs its shared interfaces. Sequencing and
sizing: `campaign/closeout/REFACTOR-PLAN.md` (to be drafted). Every chapter 3–4 family in the ledger is acknowledged
(CH34-D2, D3; D4's factorings landed in #70; ARM-1/ARM-2; SG1-UH; FE-LIVE-1), with cleanup
scheduled to the 12.2c / MIG / dedup windows. Two small follow-ups remain open under CH34-D4 (two
colleague-owned retirements, and the padding-parse uniqueness lemma). Options: carry all
acknowledged debt into `main` with a closeout register (recommended: it is already documented,
and much of it is already on `main`), or run some windows before integration.

**D5 · Integration shape.** **Ruled (Seyoon, 2026-11-16): as proposed.** As in #180: merge `main` into the campaign first (disjoint changes),
replay, then one PR from the campaign to `main` that leaves `campaign/` and `devtools/` off
`main`. Confirm, or name a different shape (for example, a squash).

**D6 · Minor normalizations.** **Ruled (Seyoon, 2026-11-16): as proposed.** `Diagonalization/Ladner.lean`'s header reads `Authors: Codex` (from
the gate 128 scaffold); every other file names people or "TCSlib Contributors". Proposed: change
it to the usual form in the integration PR. Confirm the wording.

## 3. Work packages

Each is a maintainer PR with its own gate unless marked otherwise. Codex is needed only for the
audits (and for fills if D1 = (b)).

| # | Package | Depends on | Codex use |
|---|---|---|---|
| W1 | **Done (2026-11-16, `census/`):** no campaign-introduced admission; 166 in the snapshot, 41 of them RD-2/H6; 26 public removals and 19 restatements, none used by `main`'s changed files. **Admission and statement census.** A whole-campaign inventory, maintainer-run: every direct admission in `TCSlib` at the campaign tip, classified (campaign-introduced, inherited from `main`, held); and a statement-drift check of every public chapter 3–4 declaration against its last gated version (the gates' `SOURCE.json` freezes). Records only. | — | none |
| W2 | **Done: #328 merged** (`720e2a9c`, 2026-11-16; gate 142 CLEAR 0/0/0). The chapter scope has no admission. **RD-2/H6 per D1.** (a): one removal PR, full downstream replay, gate. (b): regenerate RD-2a/b briefs, two fills, gates. (c): nothing. | D1, W1 | (a) 1 audit; (b) 2 fills + 2 audits |
| W3 | **Plan agreed (Seyoon, 2026-11-16; `REFACTOR-PLAN.md`): waves R0–R6, register §4.** **Debt register** per D4: one record listing each acknowledged family, its file, size, owner and window, carried into `main`'s backlog. Records only. | D4 | none |
| W4 | **Sync `main` into the campaign** (25 commits, disjoint), full replay on the merged tree, new snapshot. | D5 | none (records-only gate if wanted) |
| W5 | **Blueprint increment** for chapters 3–4, with the repository's `/blueprint-extract` on the synced tree (after W4, so it builds on `main`'s reorganized blueprint). One PR. | W4 | 1 audit (light) |
| W6 | **Final audit**: one Codex gate over the chapter scope: the headline and admission probes, the statement-vs-book fidelity table (plan §1), standards lint, W1's census and W3's register. | W1–W5 | 1 audit |
| W8 | ~~Exercise 3.3~~ **Deferred again (Seyoon, 2026-11-16):** the existence of `B` (`exists_oracle_ne`) matters more than `B ∈ EXP`. | — | none |
| W9 | ~~Relativized hierarchies~~ **Deferred (Seyoon, 2026-11-16), until after the other closeout work and possibly after integration into `main`.** The design note (`W9-DESIGN.md`) sizes the oracle instances at 30–40k lines for all three. **Relativized hierarchies** (D3): generalize rather than duplicate. Design note first, on one interface over machine models (plain and oracle) that the existing deterministic proof (`DiagSimulator`), the nondeterministic proof and the space proof are restated against, each instantiated twice. The oracle space hierarchy needs an oracle space class and its query-tape convention, which AB09 leaves open; the note proposes one for Seyoon. Then statement gates and fills, one hierarchy at a time. | D3 | design review, 3 fills, 3+ audits |
| W7 | **Integration PR** to `main` (shape per D5), with D6's normalization; replay on `main`'s tree. Seyoon merges. | W6 | none, or 1 audit if wanted |

**Order:** W1 now; then W2, W3, the W9 design note and the refactor plan in parallel; the refactors and
the W9 fills; W4; W5; W6; W7. **Revised (2026-11-16):** W2; the refactor waves R0–R6; W4; W5; W6; W7. W9 deferred.

**Cost, with D1 = (a):** four or five Codex audits (W2, W5, W6, optionally W7) and no fills.
With D1 = (b), add two fills and two audits.

## 4. What "done" means

Chapters 3–4 are closed when:
1. every core and core-late item of plan §1 is proved on `main` with standard axioms;
2. the chapter scope has no admission, or only the admissions D1 = (c) explicitly carries;
3. every deferred item is listed (D3), and every duplication family is either retired or in the
   carried register (D4);
4. the blueprint covers the chapters (W5);
5. the final audit (W6) is CLEAR and the integration (W7) has merged.
