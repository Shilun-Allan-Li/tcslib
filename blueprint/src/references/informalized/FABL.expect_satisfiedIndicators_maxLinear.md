<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.expect_satisfiedIndicators_maxLinear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expected number of satisfied linear constraints

**Claim.** For a finite multiset of nonempty linear constraints, each on distinct variables and requiring their sum in $\mathbb{F}_2$ to equal a specified right-hand side, the expected number satisfied by a uniform random assignment is half the multiset's cardinality.

**Proof.** Induct on the multiset. The empty multiset has satisfaction count and cardinality zero. In the step, adjoining one constraint adds its satisfaction indicator to the previous total. Linearity of expectation separates these contributions; the new constraint has expected indicator $1/2$ (`expect_satisfiedIndicator_maxLinear`), while the induction hypothesis gives half the old cardinality. Since adjoining one element increases cardinality by one, the result follows.

**Key facts.** `FABL.expect_satisfiedIndicator_maxLinear`.
