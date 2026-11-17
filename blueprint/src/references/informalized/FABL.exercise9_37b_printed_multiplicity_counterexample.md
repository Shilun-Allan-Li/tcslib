<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.exercise9_37b_printed_multiplicity_counterexample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Multiplicity counterexample for partite matchings

**Claim.** For four parts of size one, the number of encoded partite perfect matchings divided by $(1!)^4$ is not $1$.

**Proof.** The count of partite perfect matchings for four parts of size one is $3$ ($\texttt{card\_partitePerfectMatching\_four\_one}$). Since $1!=1$, the quotient is $3$, which differs from $1$.

**Key facts.** `FABL.card_partitePerfectMatching_four_one`.
