# Hash-sign Rule-10 evidence closure

All native evidence is closed at source `2e9d455a003c83d33b89149c83a6ab0610a63a4f`.

- Final whole-file seals: **20/20** owner-by-variant cells pass, with full native identity, irreducibility, mask and EOF coverage independently audited.
- Axioms: **176** stored constants audited. The target uses exactly `propext`, `Classical.choice`, `Quot.sound`; the unchanged Lamport-dependent existential retains `sorryAx`.
- Final controls: **11 pairs / 22 probes**; all unsealed controls pass, each sealed negative fails exactly once at its planned line, and every reader positive passes.
- Explicit scan: **406** items;361 theorem uses, 6 owned-definition uses, 39 local proof names, 0 foreign definitions. Native method/open aliases are separately verified.
- Historical diagnostics: **3**, all repaired and linked to latest-source passing checks.

The import-only Authentication facade has zero stored constants. Its baseline source and full request set are reconstructed from exact base Git bytes, the genuine earlier base census, and source-identical additional modules. Baseline facade checks load current compiled dependencies; this is disclosed in `base-facade-2250/catalog-reconstruction.json`, rather than represented as a pure baseline proof-tree run. Both facade baseline variants pass. Eight helper modules do not exist at the base.

Primary entry points: `final-r2/seal-matrix.json`, `final-r2/axioms-summary.json`, `final-r2/control-audit-summary.json`, `final-r2/explicit-final.json`, `final-r2/explicit-review.json`, `source-seal-failure-ledger.json`, and `FINAL-INDEX.json`.

All original and superseded preparations, tool versions, control/seal sources, request rows, raw logs and results JSONL are retained. `closed-probe-log-list.txt` lists the 74 closed Rule-10 probe logs; additional resource and bootstrap/check logs remain elsewhere in the complete evidence payload.
