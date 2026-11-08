<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPDerandomization.lean :: FABL.CSPInstance.runLocalConditionalSteps_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Work of Conditional Steps

**Claim.** Running local conditional steps through any list increases the state's work by the sum of the step-work costs for the variables in that list.

**Proof.** Induct on the list. For the empty list, the run leaves the state unchanged and the sum of costs is zero. For a list with head $v$ and tail $L$, the run first performs the step at $v$, which adds its cost to the current work, and then runs through $L$. Apply the induction hypothesis to that resulting state: the tail adds the sum of its costs. Associativity of addition combines the initial work, the head cost, and the tail sum into the asserted formula.
