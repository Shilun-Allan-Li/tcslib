<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitTail.reindexedSignRestriction_evalFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Commutes with Evaluation

**Claim.** Reindexing the restriction of the function computed by a circuit tail gives the same result as evaluating the tail on the individually reindexed restricted input functions, with the same gate.

**Proof.** Unfold the definitions on both sides. At a point of the reindexed free-coordinate cube, each side evaluates the same tail and gate on the same tuple of values: the value at each input is obtained by restricting that input function using the fixed complement assignment and the same reindexing of free coordinates. The two functions therefore agree pointwise.
