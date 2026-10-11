# B7 statement mini-phase (P4.4b) gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-11): 0 blockers, 0 majors, 3 minors, 12 notes

The findings are verbatim in `audits/b7-statements-findings.md`; the pack is
`audits/b7-statements-pack.md`. The auditor found **all seven new statements
true as stated**:

- `readIn_run`;
- N1–N4;
- `OIS.run` and `OIS.compile_decides`.

It also accepted:

- the two route changes (`audits/ch4-p44-resolutions-addendum.md`) as sound
  and free of cycles;
- the clamping table, by an exhaustive check over virtual lengths 0–64;
- placement in `Complexity.LogProg`;
- the screen, on the attached population.

This is a statement-gate verdict, not a certification of the pending
proofs.

| Finding | Disposition |
|---|---|
| 1 (minor): `compQ`'s sketch omits the empty representation of `0` and leaves the length search's stopping rule unclear | **Swept** (comment-only, `QueryReshape.lean`). The tail is canonical when it is "empty or ending in `true`". `F` is the first failing length query below the cap, or the cap itself when every query succeeds. A cap of `0` needs no query |
| 2 (minor): N1's sketch gives an exact cell count that omits workspace and boundary cells | **Swept** (comment-only, `InputAccess.lean`). Registers hold at most `\|bits (\|y\| + 1)\|` bits, each tape visits `O(logSpace \|y\|)` cells with its origin and boundary cells counted, and `compile_space` gives the bound |
| 3 (minor): T3's sketch still gives the superseded `χ_C` route | **Swept now** (comment-only, `Reductions.lean`): unpack `h`, `Set.ext`, then `mem_LOGSPACE_preimage hf hC`. The original circularity warning stays in `audits/ch4-p44-resolutions.md` as the historical record |
| 4, 5, 7, 8, 10, 11, 12 (notes): the auditor's guidance for the fill | **Carried into the B7 fill brief** as binding gate guidance (see below) |
| 14 (note): the full 53-pair screen names six source files that were not attached | **Pack practice:** state the exact screen invocation and attach its complete source population. Here the auditor's 43 → 43 replay on the attached files showed no new pair, which supports the "no new copy" result |
| 6, 9, 13, 15 (notes) | Confirmed. No action |

The three swept modules are identical with comments stripped, elaborate at
0 errors with their sorry counts unchanged, and lint clean
(`audits/logs/b7-statements-close-sweep.log`).

### Gate guidance carried into the B7 fill brief

- **`readIn_run`** (note 4). The head range does not depend on `i`; that is a
  head-motion bound only. Constructing or storing an index still costs its
  bits.
- **N1** (note 5). Compare the query's index with the counter while
  streaming, without copying it into workspace. Reject a non-canonical
  index, such as `[false]`.
- **`OIS.run`** (note 7). The oracle laws are required only on genuine
  queries. Add no law for malformed or out-of-range queries.
- **`OIS.compile_decides`** (note 8). Keep the scalar radius `B`.
- **N3** (note 10). `dropIdx` decodes pair *shape* only. The discarded and
  retained payloads are arbitrary words; do not require them to be
  canonical.
- **N4** (note 11). Handle overflow with `compQ_length_le`. The shorter
  `dropIdx` bound does not carry over.
- **Routes** (note 12). Keep the overflow, canonicality, carry and
  paired-layout obligations. The multiplication probe *assumes* the
  algorithm's correctness invariant, and the fill must prove it.

**Gate CLOSED. PR #24 is clear to merge.**
