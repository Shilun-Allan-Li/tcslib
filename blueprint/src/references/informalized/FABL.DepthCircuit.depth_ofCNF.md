<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Circuits.lean :: FABL.DepthCircuit.depth_ofCNF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth of a CNF Circuit

**Claim.** The circuit associated with any conjunctive normal form formula has depth $2$.

**Proof.** The associated circuit has an initial layer of clause gates and a tail consisting of the single output layer. Thus the tail has layer count one, and the circuit depth, which adds the initial layer, is $1+1=2$. This is the definitional computation captured directly by the proof.
