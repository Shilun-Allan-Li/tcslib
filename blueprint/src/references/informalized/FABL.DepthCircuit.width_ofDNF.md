<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.width_ofDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of the DNF circuit

**Claim.** For a DNF formula on $n$ coordinates, the width of the circuit formed from its terms as its first layer of AND gates equals the width of the formula.

**Proof.** The circuit construction places exactly the formula's terms in its first layer. Circuit width is defined as the width of the DNF formed from that first layer, so substituting the formula's term list gives precisely the formula's width.
