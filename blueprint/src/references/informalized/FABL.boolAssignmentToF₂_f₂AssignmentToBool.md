<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.boolAssignmentToF₂_f₂AssignmentToBool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean and binary field assignments

**Claim.** For any set $V$ and assignment $a:V\to\mathbb{F}_2$, converting its values to Booleans and then back to $\mathbb{F}_2$ recovers $a$.

**Proof.** Evaluate both assignments at an arbitrary variable $v\in V$. The Boolean-to-field conversion is the inverse of the field-to-Boolean conversion, since both are defined using the same equivalence between Booleans and $\mathbb{F}_2$. Applying an equivalence and then its inverse returns the original value, so the two assignments agree at every variable and hence are equal.
