# Maintainer tooling follow-ups

## Gate 04 round 5, R5-01: anonymous commands

**Open.** The term collector's source tier enumerates stored constants and supplemental named
lemma statements. A standalone anonymous `example` can have no stored constant and be the sole
reader of a foreign definition. The auditor demonstrated this with `HiddenNat`; merely collecting
every stored constant does not close the gap.

Before relying on this collector alone for a future whole-file review:

- collect and check anonymous commands, or seal a conservative list of ordinary foreign TCSlib
  definitions from the module's import closure;
- retain the existing private/generated-helper traversal, approved notation handling and the
  explicit-unfold check;
- add a control whose only foreign-definition read is in an anonymous command: it closes unsealed
  and fails sealed.

The collector implementation is Lean. Any change to its `.lean` source goes through a PR under
the standing Lean-only-by-PR rule. Gate 04's head was independently covered by the auditor's
broader 6,322-pair import-closure seal; that result is not a repair of the collector.

The scanner's separate blank/comment-only continuation bug is **fixed** in the round-5 review:
12 text-parser regression cases pass, and the hardened scan of the audited head remains 0/0/0.
It remains a TCSlib-name text scanner, not a complete Lean syntax or core/Mathlib unfold check.

For gate 08 intake, account for this coverage qualification if the same stored-constant collector
is used; do not inherit an unqualified whole-command-coverage claim from its presence.

Source: [Gate 04 round 5 resolutions](../gates/04-s2b/resolutions-r5.md) and the verbatim findings.

## Gate 08 round 2: head-specific conservative coverage

At `84f35910912bd3d1cd520beea9469e0ed45ce504`, the supplement in
`gates/08-shared/evidence-r2/` checks 13,056 import-closure pairs: 12,966 active local seals
and 90 already irreducible pairs. It covers anonymous commands conservatively and includes
a standalone anonymous control under the full RSA seal. This does **not** close the general
collector implementation issue above. Numerical and hygienic private Names are resolved from
the environment; failed attribute/harness attempts are excluded before classification.

The 17 failing untouched declarations all have code identical to the checked base (comments
and following namespace commands excluded); broad base seals were not rerun. Fifteen match
the historical 764-row inventory. Two additional inherited rows must be reconciled at the
clean-up issue base: `Randomized/Build/IterateFind.polyTimeComputable_find` and
`NumberTheory/Primality.exists_samplePrime_nuppt`. See `conservative-failure-preservation.json`
and `historical-cleanup-reconciliation.json` for exact module names, lines and hashes.
This is a recorded inventory input, not a fill dispatch or a claim those proofs are repaired.
