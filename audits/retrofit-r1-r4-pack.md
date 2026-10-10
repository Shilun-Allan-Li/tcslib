# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 4

Round 3 (`audits/retrofit-r1-r3-pack.md`, findings verbatim in
`audits/retrofit-r1-r3-findings.md`) **closed R2-2 (the RB4 human
acknowledgment accepted) and R2-3**, verified the listed Catalog subset,
the Wrappers row, and the corrected named-family arithmetic — and held the
gate on **R3-1**: the Catalog membership was still incomplete under the
ledger's own union rule (the two in-file originals missing; the declared
Composition and counter-block copies unaccounted), with two minors (the
A2 report absent from the bundle; the Wrappers line estimate). This round
audits the completed accounting. The gate closes on zero blockers and
majors.

## Disposition table (verify each)

| Round-3 finding | Disposition |
|---|---|
| R3-1 (major: Catalog membership incomplete) | **Completed by maintainer reconciliation, declaration by declaration, against the attached sources.** The ledger's Catalog row now counts the union of both sides once per file: the listed 264 copy-side subset **+ 2 in-file originals** (`f2_finSumEquiv`, `f2_sum_add`) **+ 3 Composition-sourced copies** (`f2_idTM`, `f2_idTM_run`, `f2_constTM` — normalized-identical to the attached `Composition.lean` originals) **+ 20 counter-block members** — the reconciliation you demanded: **19 of the 20 are normalized-identical** to `ClassP/TimeConstructible.lean`'s originals (`counterInc` … `counter_emit`), and `f2_counter_computes` is a **near-copy adaptation of the proof body of the public `timeConstructible_id`** (its attributed source; no declaration named `counter_computes` exists there). Total **289/423 = 68.3%** — your conditional subtotal, now unconditional; strict-normalized **283/423 = 66.9%** (excluding the 5 strengthened counterparts and the near-copy). The remaining 29 F2A entries outside all partitions are reconciled as **new space-proof material, not copies**; the A2 report's 45 declarations contribute 2 + 1 members and 42 new constructions. Two new original-side rows added: `TimeConstructible.lean` 20/21 = 95.2% and `Composition.lean` 3/19 = 15.8%. **Recompute the reconciliation yourself from the attached three sources** (normalized comparison after consistent `f2_` substitution) and flag any verdict you cannot reproduce or any member still missing. |
| R3-2 (minor: the A2 report absent) | **Attached** (`audits/vhost-agent-reports/` is the vhost report; the Catalog continuation A2 report is `audits/routine-f1-agent-reports/batchF2A2-REPORT.md`, attached this round), together with the corrected provenance mapping above. |
| R3-3 (minor: Wrappers ≈450) | **Fixed**: the ledger carries your exact span count, 297 (77 redirect + 220 timed), and your 5,754 + 30 Catalog-subset measurement, with the counter/Composition blocks' ≈320 marked as a maintainer estimate under the same rule. |
| R3-4 — R3-8 (verified subsets, acknowledgment closure, carried evidence) | Carried as recorded; this round's delta is the ledger, this pack, and the plan's decision log — no Lean source changed. The D-R2/D-R3/RB4 acknowledgments stand; nothing here requests re-approval. |

## Brief for the auditor

1. Reproduce the counter-block reconciliation from the attached
   `Catalog.lean` and `TimeConstructible.lean` (19 identical + 1 near-copy
   with its stated source), the Composition family from the attached
   `Composition.lean`, and the in-file pair arithmetic; verify the 289 and
   283 totals and the two new original-side rows' denominators (21 and 19
   explicit declarations).
2. Verify the 29-entry "new space material, not copies" remainder claim
   on a sample of your choosing (the F2A inventory is attached via its
   report; the entries name their roles).
3. Check the ledger's acknowledgment table still satisfies the template's
   debt dispositions after the rebuild (nothing moved: D-R2's 12.2c, the
   user's RB4).
4. Report in the standard table; findings verbatim into
   `audits/retrofit-r1-r4-findings.md`; the gate closes on zero blockers
   and majors, retiring epoch R1 and arming 12.2c and RB4.

## Repository-side attestations

As rounds 1-3, unchanged; this round's delta is documentation only.
