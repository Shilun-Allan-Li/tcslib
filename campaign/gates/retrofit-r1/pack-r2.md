# External audit pack — chapter-1/2 retrofit, epoch R1 boundary, round 2

Round 1 (`audits/retrofit-r1-pack.md`, findings verbatim in
`audits/retrofit-r1-findings.md`) returned **0 blockers, 2 majors, 2
minors, 8 notes** — no code defect; both majors are evidence-packaging
gaps, both supplied here. Audited at commit `fb721402` (the three retrofit
target files are byte-identical there to the post-merge state your round-1
report analyzed; the tree's other changes are the out-of-scope §13
surface). The gate closes on zero blockers and zero majors; debt majors
close only by human acknowledgment.

## Disposition table (verify each)

| Round-1 finding | Disposition |
|---|---|
| R1-1 (major: no complete sources; the public Encoding lemma absent) | **Supplied.** The three complete **final** source files are attached in full (`Build/Loop.lean` 5,515, `Build/Primitives.lean` 6,374, `CookLevin/Hardness.lean` 8,725), together with the three patch series — reverse-apply them to reconstruct the base `5588628c` states and redo the full byte comparisons and blob arithmetic. `Encoding.lean` is attached in full: the public `Turing.eq_pairEncode_of_pairDecode` (line 231, with its namespace and variable context) against the deleted private's quoted proposition — perform the literal statement comparison the E1 approval assumed. |
| R1-2 (major: no cumulative duplication ledger) | **Supplied**: the standing `audits/duplication-ledger.md` (attached) — the counting convention (twin-map membership per the retrofit inventories), per-file original-/copy-side totals and declaration fractions, approximate twin-block lines, the epoch delta (0 new copies; 245 → 233 original-side members; one pair collapsed by the approved E1), and the disposition column carrying the recorded D-R2/D-R3 acknowledgments and the 12.2c schedule. Headline honesty: `Build/Catalog.lean` stands at **59% copied material by declarations** — acknowledged debt with a named resolution window, per your proposed fix no fresh approval is requested. Verify the ledger's arithmetic against the attached inventories and sources; flag any family the convention misses. |
| R1-3 (minor: −83, not −85; double-listed `catalogPair_length`) | **Erratum acknowledged** in the plan's decision log: −1,639 lines, **−83** private declarations (76 dead + 7 eliminated by replacement, your distinction adopted); `catalogPair_length` counted once. Shipped round-1 pack stays verbatim. |
| R1-4 (minor: Loop public count; post-E1 freeze wording) | **Erratum acknowledged**: Loop 8 / Primitives 18 / Hardness 5 publics; all 31 signatures/statements/docstrings unchanged; 30/31 complete declaration texts unchanged, with the one authorized E1 proof-body substitution; the agents' 18/18 attestation preserved as the historical pre-E1 statement. |
| R1-5 — R1-12 (notes) | Carried as recorded; your "76 dead + 7 replaced" accounting, the H4/`clFreshTM`/swap verifications, the E1 trail verification, and the evidence-boundary distinctions are adopted into the resolutions at close. |

## Brief for the auditor

1. Reconstruct the three base files from the attached finals and patch
   series; re-establish the public-declaration byte comparisons you could
   not complete in round 1 (Loop 8/8, Hardness 5/5, Primitives 18/18
   pre-E1 and 17/18 complete bodies post-E1 with the authorized line).
2. Perform the literal E1 statement comparison: the deleted
   `catalogPair_inverse` proposition against the attached public
   `Turing.eq_pairEncode_of_pairDecode`, in context.
3. Verify `audits/duplication-ledger.md`: the convention's fit to the
   attached inventories, the per-file counts and fractions (recompute at
   least the Loop 87 and Primitives 146 original-side figures and the
   Catalog partition), the epoch delta, and the acknowledgment state. If
   any accumulated debt lacks a named owner and window, that is a debt
   major requiring human acknowledgment.
4. Report in the standard table; the gate closes on zero blockers and
   majors.

## Repository-side attestations

As the round-1 pack, unchanged: the per-batch replays, independent axiom
prints (8 + 18 + 5, no `sorryAx`), lint, checksums, bundle verifications,
shim exclusions, and the side-branch/PR merge trail.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md` (failure mode 5 in force);
findings verbatim into `audits/retrofit-r1-r2-findings.md`.
