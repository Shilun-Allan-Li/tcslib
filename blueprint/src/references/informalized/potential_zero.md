<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Hedge/Basic.lean :: potential_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial potential

**Claim.** At time zero, the Hedge potential equals the number $N$ of experts.

**Proof.** At time zero, there are no rounds with index less than zero, so the sum defining each expert's cumulative loss is empty and equals zero. Consequently each weight is $e^0=1$. Summing this constant value over the $N$ experts gives $N$.
