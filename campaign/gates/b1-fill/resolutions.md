# Epoch 2 B1 fill gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 2 minors, 17 notes

The findings are verbatim in `audits/b1-fill-findings.md`; the pack is
`audits/b1-fill-pack.md`. The auditor:

- reconstructed every after-source from the patch;
- confirmed the freeze: 94 publics unchanged, 20 added, and the bodies
  changed only at the eight targets, `queryString_length_le` and E5;
- restated and accepted every new P0 contract, including the plain-run
  bridge and the query-tape capture;
- confirmed route fidelity for all eight proofs;
- reproduced the screen on every attached population.

| Finding | Disposition |
|---|---|
| 1 (minor): the fill's fresh-length condition `nᵢ ^ i + i < 2 ^ nᵢ` is weaker than the sketch's `2 ^ (nᵢ / 10) > nᵢ ^ i + i` | **Swept** (comment-only). `exists_oracle_ne`'s sketch states the condition the proof uses. The supersession is recorded as a route note in `audits/b1-integration.md`. `Relativization.lean` is identical with comments stripped and elaborates at 0 errors (`audits/logs/b1-fill-close-sweep.log`) |
| 2 (minor): the cumulative per-file accounting for B1 is missing | **Added** to `audits/duplication-ledger.md`, new section "Epoch 2, B1". It gives member sets, totals and fractions for `Oracle`, `Deterministic`, `Finite` and the three FH-1 files, and how FH-1 relates to Catalog and Loop. The four screen hits that are not members are listed with their dispositions. No file crosses one fifth, and no file gains a copy in this epoch |
| 10 (note): `Build/Wrappers.lean`'s capture definitions were not attached | Accepted. They are received-library evidence |
| 17 (note): Catalog was identified by blob only, so its 54% glue pair could not be re-run | Accepted on the supplied evidence. **Pack practice:** attach every comparison source, unchanged ones included. The §12.8 pack already does |
| 19 (note): two deferred publics in the axiom log still print `sorryAx` | **Correction recorded:** the pack's "no `sorryAx`" claim covers the 20 new publics and the eight filled targets, not the whole log. The two are the two out-of-scope sorried publics, `POracle_eq_P_of_mem_P` (deferred to the oracle-call extension) and the headline `baker_gill_solovay`, as expected |
| 3–9, 11–16, 18 (notes) | Confirmed. No action. Note 4's FH-1 reading, a scheduled retirement rather than seven replacements already made, matches `backlog.md` FH-1 |

**Gate CLOSED. PR #26 is clear to merge.**
