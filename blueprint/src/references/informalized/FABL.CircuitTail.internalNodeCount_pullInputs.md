<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitTail.internalNodeCount_pullInputs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Internal Node Count After Pullback

**Claim.** Pulling a circuit tail's inputs back along an injective map leaves its number of internal nodes unchanged.

**Proof.** Split into the two forms of a circuit tail. For an output tail, both the original and pulled-back output have zero internal nodes. For a layered tail, pulling back maps the list of gates to a new list of the same length; the remaining tail is cast to the length of this mapped list. Its internal node count is unchanged by that cast. Hence the total, which is the number of gates in the first layer plus the count for the remaining tail, is unchanged.
