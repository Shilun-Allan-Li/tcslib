<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.FiniteDecisionTree.toF₂Real_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-Valued Conversion Preserves Computation

**Claim.** If a sign-valued finite decision tree computes a Boolean function, its corresponding binary decision tree computes the real-valued function obtained by converting binary inputs to signs and interpreting the output sign as a real number.

**Proof.** Fix a binary input. The evaluation identity `eval_toF₂Real` says that evaluating the converted tree equals converting to a real number the output of the original tree on the corresponding sign input. Since the original tree computes the target, that output is the target's value on that sign input. This is precisely the value of the stated real-valued function, so the converted tree computes it on every input.

**Key facts.** `FABL.FiniteDecisionTree.eval_toF₂Real`.
