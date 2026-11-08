<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.SignPredicate.randomizedValue_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Randomized Acceptance

**Claim.** When every coordinate mean lies in $[-1,1]$, the randomized value of a Boolean predicate lies in $[0,1]$.

**Proof.** The randomized value is the expectation under a probability distribution of the predicate’s indicator. That indicator is pointwise either $0$ or $1$, hence lies in $[0,1]$. The expectation of any function valued in this interval also lies in the interval (\texttt{FABL.pmfExpectation_mem_Icc_zero_one}).

**Key facts.** `FABL.pmfExpectation_mem_Icc_zero_one`.
