<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dedupClauseVars_nodup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Deduplication leaves no duplicate literals

**Claim.** For any clause `c : List (Literal n)`, the list `dedupClauseVars c`
has no duplicates: `(dedupClauseVars c).Nodup`.

**Proof.** Two lines.

1. `List.pairwise_pwFilter` says the output of `pwFilter r` is `Pairwise r`; here
   `r l₁ l₂` is `l₁.var ≠ l₂.var`.
2. `Nodup` is `Pairwise (· ≠ ·)`, and distinct variables force distinct
   literals, so `List.Pairwise.imp` weakens the relation — `convert … using 1`
   then `grind`.

**Used in.** `cleanCNF_D3_nodup`; a deliberately granular helper, one of the two
per-clause hygiene conditions the switching lemma requires.
