<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadTests.lean :: FABL.oddBLRBookBoundCounterexample_refutes_printed_inequality -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure of the Printed Inequality

**Claim.** For the negative OR function on the two-dimensional sign cube, the proposed upper bound using the maximum odd Fourier coefficient is strictly less than the Odd BLR test's acceptance probability.

**Proof.** The acceptance probability for this counterexample is $3/8$ (`oddBLRBookBoundCounterexample_acceptance`), while the proposed right-hand side is $1/4$ (`oddBLRBookBoundCounterexample_printed_rhs`). Since $1/4<3/8$, the displayed inequality fails for this function.

**Key facts.** `FABL.oddBLRBookBoundCounterexample_acceptance`, `FABL.oddBLRBookBoundCounterexample_printed_rhs`.
