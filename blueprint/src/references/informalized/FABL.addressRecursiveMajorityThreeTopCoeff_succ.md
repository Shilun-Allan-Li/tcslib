<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveMajorityDecisionTrees.lean :: FABL.addressRecursiveMajorityThreeTopCoeff_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Top Coefficient Recurrence

**Claim.** For every depth $d\in\mathbb{N}$, the top coefficient of the depth-$(d+1)$ recursively composed three-input majority function equals minus one half the cube of the depth-$d$ top coefficient.

**Proof.** Fix a depth $d$. Regard each of the three depth-$d$ input blocks as a sign-valued function $F$, and let $P$ be the product of all input signs in a block, its full parity. Under the uniform distribution on blocks, the mean of $P$ is zero, since the full parity has mean zero. Re-index the expectation on the depth-$(d+1)$ inputs as an expectation over triples of independent blocks. The three-input majority sign is $(F_1+F_2+F_3-F_1F_2F_3)/2$, while the parity of all inputs is $P_1P_2P_3$. The resulting expectation is therefore the expectation of this majority expression times the product parity. The majority-parity averaging identity, when the block parity has mean zero, says this expectation equals $-1/2$ times the cube of the single-block correlation $\mathbb{E}[FP]$. That single-block correlation is exactly the depth-$d$ top coefficient by definition, proving the recurrence.

**Key facts.** `FABL.expect_fullParity_eq_zero`, `FABL.signValue_majority_three`, `FABL.expect_majorityThreeParity_step`.
