<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.positiveLearningParameter_toReal_mem_Ioc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real-Valued Learning Parameter Bounds

**Claim.** If a rational learning parameter lies in $(0,\tfrac12]$, then its real image also lies in $(0,\tfrac12]$.

**Proof.** The rational parameter is positive, and the rational-to-real embedding preserves strict positivity, so its real image is positive. The embedding also preserves order, so the rational upper bound by $1/2$ gives the same upper bound in the reals.
