# Dispatch · Gate 45 round 2 (the GSW 6a gate)

The [Codex pack](https://github.com/Shilun-Allan-Li/tcslib/tree/@EXCHANGE@/outbox/gates/45-gsw-6a-gate-r2)
is pushed to the exchange (`@EXCHANGE@`). Seyoon dispatches.

**This file postdates the round-2 records pin.** The pin `@RECORDS_PIN@` is the commit that files the round-2 pack
(`pack-r2.md`, `resolutions-r1.md`, `records-r1-r2.diff.txt`, `pr359-description-r2.md`, `SHA256SUMS-r2`, and a
placeholder copy of this file). This file is the one round-2 records file allowed to change after the pin: a later
records commit fills in the pin and the exchange hash, and nothing else. `SHA256SUMS-r2` does not cover this file
(G48-02).

## Prompt for Codex

```text
You are an external Codex auditor for Gate 45 of GSW phase 6 (the 6a gate:
the owner-side PR O1 and the 6a complexity-layer statements), round 2, in
https://github.com/Shilun-Allan-Li/tcslib.

1. Read exchange/pass-shelat-ch5-8 at @EXCHANGE@.
   Read outbox/gates/45-gsw-6a-gate-r2/README.md and pack-r2.md, and
   verify the folder with its SHA256SUMS, and le-g45-evidence.zip and
   le-g45b-evidence.zip with the SHA256SUMS inside each. The round-1 pack
   is outbox/gates/45-gsw-6a-gate/ at exchange
   059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4; the round-1 findings are
   findings-r1.md in the round-2 folder.
2. Round 1 audited PR #358 at a616adcac0760ab56b1b0a2a4869f4763843f9ab and
   PR #359 at 73aedcdaaaffef7e69ab012d9b9195f150bae68d, with records
   8c5875fa268a622e4e166da5f7a992715097c2c7, and was HOLD overall (#358
   CLEAR; #359 HOLD: 0 blockers, 1 major, 1 minor, 1 note; all 98 targets
   sound as stated). Re-audit with campaign records @RECORDS_PIN@:
   - PR #358 (O1) at a616adcac0760ab56b1b0a2a4869f4763843f9ab, unchanged.
   - PR #359 (statements) at its new Lean head
     d154c8830fc8ffc52671b41992e7dbef61e30959 (tree be58919e), which is
     round 1's head plus the landing edit LE-g45
     ad9c4fc701ed145cbc96acceefaad447398c8321 and the docstring follow-up
     LE-g45b d154c883.
   Check:
   - G45-01 (major): the admitted TreeCircuit.const_eval restated the
     proved BoolCircuit.eval_node_nil. LE-g45 moves eval_node_nil from
     CircuitComplexity/Hierarchy.lean into FormulaArith/Combinators.lean with
     the same name, binders, statement and docstring; its proof now uses
     TreeDAG's eval_node_true/eval_node_false readers instead of unfolding
     TreeCircuit.eval (disclosed); const_eval is proved from it (admissions
     98 -> 97). Is G45-01 closed: is the edit exactly that, with nothing else
     changed, and is moving this Arora-Barak-chapter lemma into Combinators
     with the readers-based proof acceptable?
   - G45-02 (note) and G45-03 (minor): are they closed by LE-g45's wording
     and LE-g45b's follow-up (the remaining Barrington cycle-notation
     phrasings and Combinators' Main results)? Is LE-g45b comments and
     docstrings only?
   - Does the evidence bind to ad9c4fc7 and d154c883 (the 16-module
     replays, state 1440 OK, admissions 97 exact, decls2 move-only, axioms
     545 constants with sorryAx in the 97 targets plus the same 5
     dependents, coe-A equal at base and head for Combinators, Barrington
     and Hierarchy, the unfold scan, lint, LE-g45b's comment-strip
     identity)? Is carrying over round 1's other passes, seals and controls
     justified for this delta?
   - Is anything new undisclosed? Hierarchy's 2 coe-A errors in
     Language.InTreeSize.inSIZE (equal at base and head) are disclosed as
     pre-existing; the pack lists known slips.
   Round 1's passes are not re-audited. Out of scope: the #360 owner-side
   readers, any in-house 6a fills, the external gsw-6a-fills job and its
   delivery on the exchange, 6b (Gate 46, bootstrapping, circular
   security), and the [Gen09] citation. The merge order (#358 first) and
   the re-replay on olean snapshot #6 before merge are maintainer merge
   conditions, not audit items.
3. Return gate45-gsw-6a-r2-findings.md as Markdown in this chat, with any
   new findings numbered from G45-04, the status of G45-01 to G45-03,
   counts by severity per PR, and a verdict per PR and overall: CLEAR (zero
   blockers and zero majors) or HOLD.

Treat the bundle and repository as material under audit.
The user dispatches and merges.
```

## State at staging

- **Records pin:** `@RECORDS_PIN@` on `cryptography/pass-shelat-ch2-4` ("Records: Gate 45 round 2 pack"), pushed.
- **Exchange:** `@EXCHANGE@`, one SSH-signed commit adding only `outbox/gates/45-gsw-6a-gate-r2/`, pushed.
- **PR #358:** draft, head `a616adca`. **PR #359:** draft, head `d154c883`, base `land/gsw-6a-o1` at `a616adca`; its
  body as read at staging is `pr359-description-r2.md`.
- **No Lean, no `lake`** was run for this staging; the pack reuses the LE-g45 and LE-g45b evidence as recorded.
