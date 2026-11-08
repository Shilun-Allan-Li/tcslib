<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.f₂AssignmentToBool_boolAssignmentToF₂ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean assignment round trip

**Claim.** Converting a Boolean assignment to values in $\mathbb{F}_2$ and then back to Boolean values recovers the original assignment.

**Proof.** Evaluate both assignments at an arbitrary variable. The conversion to $\mathbb{F}_2$ applies the equivalence from Boolean values to $\mathbb{F}_2$, and the conversion back applies its inverse. An equivalence followed by its inverse recovers the original Boolean value, so the assignments agree at every variable.
