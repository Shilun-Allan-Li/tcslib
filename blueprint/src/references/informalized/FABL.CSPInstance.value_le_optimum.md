<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.CSPInstance.value_le_optimum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment Value Bounded by the Optimum

**Claim.** With a finite nonempty domain and a finite variable set, every assignment's value is at most the maximum value over all assignments, which is the instance's optimum.

**Proof.** The assignment space has a maximizing assignment because the domain and variable set are finite and the domain is nonempty. The chosen maximizing assignment is the one used to define the optimum. By the defining property of this maximum, the value of any assignment is at most the value at that chosen assignment, hence at most the optimum.
