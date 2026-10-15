# Resolutions — zone/virtual-input layer (§13), tranche A-S1 fill gate

Loop summary for the vhost-f1 fill-gate audit (`audits/vhost-f1-pack.md`,
bundle sha256 `ea9dd29d…`, audited at `724108dd`). Findings preserved
verbatim in `audits/vhost-f1-findings.md`.

## Outcome

**Round 1: PASS — 0 blockers, 0 majors, 1 minor, no new duplication-debt
finding. The A-S1 fill gate is CLOSED — tranche A-S1 is complete end to
end** (statements → statement gate, 1 round → fill, 11/11 → fill gate,
1 round). `Build/VirtualInput.lean` and the Z5 statements of
`Simulation.lean` are proved, kernel-checked, and audit-verified.

The auditor independently: restated the sole new private
(`vhostSilent_layout`) and re-derived its two-way partition arithmetic
(`m = 0` included); checked all eleven proofs against the binding
statement-gate routes body by body (the visited-set **equalities** proved
pointwise, the coefficient-one space sums with no output term, the
emitting-halt derivation, the two silent contracts as pure two-layer
citations with **no third induction**, the agreement transfers' strict-
prefix guards intact); verified both declared techniques benign (the
`Unit` control mapping reduces input position and read definitionally and
restricts nothing; both `sum_bij` partitions proven surjective — nothing
discardable); re-established the freeze from the patch (203 added lines,
eleven removals each exactly `sorry`, one private added) with
reverse/forward blob reconstruction, and isolated the post-fill header
refresh as doc-only via the delivery files; and verified the ledger line
("new copies: none") under failure mode 5.

## Disposition of the finding

| # | Severity | Disposition |
|---|---|---|
| F1-1 | minor | **Pack erratum acknowledged** (shipped pack stays verbatim): `VirtualInput.lean` was 506 lines at delivery and **508** in the audited post-refresh source (the maintainer's two-line status-header refresh); `Simulation.lean` 1,014 throughout. |

## Carried

* Evidence boundaries as stated (F1-9): the replay/axiom/lint logs were
  inspected, not re-executed; kernel evidence remains the maintainer's
  independent logs (`audits/logs/vhost-f1-*`).
* The Z1/Z5 public surface is now proved infrastructure for its
  customers: the `NP^EXPCOM ⊆ EXP` query simulation, the 12.2c dedup, the
  two-tape universal (stage 1), and **RB4** — whose acknowledged window
  ("after the A-S1 fill gate closes") this close opens.

## Gate state

| Item | State |
|---|---|
| §13 tranche A-S1 | **COMPLETE** (statements, gate, fill, fill gate — all closed) |
| §13 tranche A-S2 statement gate | CLOSED (round 3); fill briefs next |
| RB4 (H3 + relocation-family dedup) | **window open** |
