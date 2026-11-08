<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.mem_to3SATAux_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in the Recursive Encoding

**Claim.** A 3-clause occurs in the recursive encoding of $cs$ from index $idx$ exactly when it occurs in the encoding of some clause at its corresponding shifted index $idx+i$, for a position $i<|cs|$.

**Proof.** We induct on $cs$. For the empty list, neither membership nor the existence of such a position is possible. For a list with head clause and tail, the output is the concatenation of the head’s encoding and the tail’s recursive encoding. Membership in this concatenation means membership in one of those two parts. Membership in the head part corresponds to position $0$. By induction, membership in the tail part corresponds to some tail position $i$; in the original list this is position $i+1$, and its encoding index agrees because $idx+(i+1)=(idx+1)+i$. Conversely, position zero gives head membership, while any positive position shifts down by one and invokes the induction hypothesis. Thus both directions hold.
