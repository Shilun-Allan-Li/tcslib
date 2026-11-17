<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.reindexBooleanFunction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation After Boolean-Function Reindexing

**Claim.** Evaluating the reindexed Boolean function at $x$ gives the original function evaluated on the input whose coordinate $i$ is $x_{e(i)}$.

**Proof.** By definition, the reindexed function sends an input $x$ to the original function evaluated at the input formed by assigning coordinate $i$ the value $x_{e(i)}$. Unfolding that definition gives the stated equality directly.
