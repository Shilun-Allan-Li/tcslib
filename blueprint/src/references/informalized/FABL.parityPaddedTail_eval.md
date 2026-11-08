<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityPaddedTail_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Padded Parity Tail

**Claim.** The padded parity tail, evaluated on the bottom layer values, equals the parity tree value at depth $q+2$ on the input $x$.

**Proof.** First unfold the padded tail as a bottom layer followed by the standard tail. The cast in its definition only adjusts the indexing type to the actual length of the bottom layer; the evaluation-through-cast identity (FABL.circuitTail_eval_cast) expresses the result as evaluation of the standard tail on the correspondingly reindexed values. The bottom next-layer evaluation identity (FABL.eval_parityBottomNextLayer) identifies each such value with the OR layer value for the depth-one parity tree assignments. Thus the remaining expression is the standard tail evaluated on those assignments. Its evaluation theorem (FABL.parityStandardTail_eval), with starting depth $1$ and gate OR, gives the parity tree value at depth $1+q+1=q+2$.

**Key facts.** `FABL.circuitTail_eval_cast`, `FABL.eval_parityBottomNextLayer`, `FABL.parityStandardTail_eval`.
