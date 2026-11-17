<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.depth_ofDNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a DNF Circuit

**Claim.** The circuit associated with any disjunctive normal form formula has depth $2$.

**Proof.** The associated circuit has an initial layer of term gates and a tail consisting of the single output layer. The tail therefore has layer count one, so the depth is $1+1=2$. This follows directly by unfolding the definitions.
