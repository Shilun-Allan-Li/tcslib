# Overnight plan, 2026-11-16 (maintainer, under Seyoon's authorization)

Seyoon (2026-11-16, before sleeping): proceed as far as possible on each thrust; the maintainer may
carry out statement prep, cleanup (deduplication etc.) and fills on its own; everything is audited
by Codex in the morning; stop at a mission-critical audit if continuing would be unsafe. Seyoon still
merges; nothing is merged overnight.

## Queue (olean trees `dl-oleans`, `dl-oleans-2`; one job per tree; disk ~2.3 GB)

1. **Deliveries** (watched every 5 minutes): `sc-yao` final, `gsw-security` final. Each: review →
   landing branch with LE edits → draft PR → Codex gate pack staged for the morning.
2. **gsw-core** (final in): review → landing → draft PR → gate pack.
3. **#331 pairings**: full build of the updated head `39d42e23` on the tip → push → Gate 40 round 2
   pack.
4. **#327 / #324**: cross-build on the tip with #332, #333 → mark clear (merge #327, then #324).
5. **Pairing fills** (maintainer-run Claude fills, proved-modulo on `stmt/pairings`): `pair-bdh`
   (T1) first; then `bb1-machine` (T4) and `bb1-sim` (T2, T3). Flagged as pending Gate 40 round 2;
   T2's relational simulation step uses a common augmented state or a shared lemma in `Games`
   (Gate 40 note), never a private host.
6. **Cleanup**: DW-5 (derand typed-view readers) and the DW-4 deduplications on merged code;
   items touching open PRs wait for their merge.
7. **GSW phase 6 prep**: DW-7 Markdown transcriptions of the passages used (GSW13, AP14, BV14;
   Pei16 §5.4.3, §6.1.2–6.1.3), then the BV14 bootstrapping plan section and questions.

## Judgment calls (Seyoon may override)

- **DW-1/DW-2 (uniform simulators) stay deferred**, as ruled ("after merging into main"): they
  change security definitions, not cleanup.
- Pairing fills proceed before Gate 40 round 2: round 2 checks LE-gate40 only, and the game and
  BB1 definitions the fills prove against did not change.
