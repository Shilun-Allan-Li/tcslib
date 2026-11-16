# Gate 40 round 2 supplement: seals on the merged head

The LE-gate40 seals ran on the `70c1f444` closure (base `523d80d2`). After the merge onto the
records tip, #326's `DTIME`/`IterateFind` changes and (for the `AdvancedEncryption` facade) #333's
GSW modules entered five owners' closures. This supplement re-runs the canonical suite at the head
`9e7a96481785d6cac4dea3b2e990c49ac278b060` on the merged tree, with LE-gate40's tools unmodified.

- **Build:** the closure of the 10 owners plus the `Pairing` and `KeyExchange` aggregators, 109
  modules; 41 built, 41/41 rc 0, 0 `error:`/`error(`; state check OK.
- **Seals** (strict A/B, coe A/B; coe-A canonical; `-DmaxErrors=0`): each 10/10, rc 0, 0 errors in
  both forms, no failing declaration; 79 probes bound to `git show 9e7a9648:<path>` hashes.
- **Controls:** strict and coe ALL_OK True; 43 sealed negatives each failing exactly once per
  harness; error vectors identical to LE-gate40.
- **Explicit-unfold scan:** identical to LE-gate40 (164 items, 0 foreign).
- **Request-set differences from LE-gate40** (additions only): +4 rows in `Operations`,
  `BonehBoyenMachine`, `BonehBoyenSecurity`, `IdentityBased` (#326's `IterateFind` match helpers);
  +148 in the `AdvancedEncryption` facade (those 4 plus 144 GSW definitions now in its closure).
- **Restore:** `dl-oleans` back to `457ba704…` (SNAPSHOT EQUAL).

Evidence: `gate40-seals-merged-evidence.zip` (`5b3b5203…`), `PROVENANCE.txt`, `evidence-SHA256SUMS`.
