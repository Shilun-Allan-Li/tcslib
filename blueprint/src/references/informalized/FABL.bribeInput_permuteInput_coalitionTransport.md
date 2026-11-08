<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.bribeInput_permuteInput_coalitionTransport -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribing Under Coalition Transport

**Claim.** Under the permutation transporting $A$ to $B$, bribing $A$ after permuting the input agrees with permuting the input obtained by bribing $B$.

**Proof.** Fix a coordinate $i$ and compare the two sides there. The transport permutation sends $i$ into $B$ exactly when $i$ lies in $A$ (`mem_coalitionTransportPerm_iff`). If $i\in A$, the left side is therefore set to $b$, and the permuted, $B$-bribed vector on the right also reads the value $b$. If $i\notin A$, its image is outside $B$, so neither side replaces the corresponding original value; both read the input at the transported coordinate. Hence the sides agree at every coordinate.

**Key facts.** `FABL.mem_coalitionTransportPerm_iff`.
