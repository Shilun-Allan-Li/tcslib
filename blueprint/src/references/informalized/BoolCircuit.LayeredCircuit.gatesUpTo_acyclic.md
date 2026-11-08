<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LayeredDAG.lean :: BoolCircuit.LayeredCircuit.gatesUpTo_acyclic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acyclicity of Bounded Gate Lists

**Claim.** For every natural number $m$, the list formed from the first $m$ layers of gates is acyclic: every source index of the gate at position $i$ is less than $n+i$.

**Proof.** Proceed by induction on the number of layers included. With no layers, the gate list is empty, so the condition holds vacuously. Suppose it holds through layer $m$, and consider a gate at position $i$ in the list through layer $m+1$. If $i$ lies in the earlier list, the induction hypothesis gives the required bound. Otherwise the gate lies among the newly appended gates from layer $m$. The definition of this list forces $m$ to be below the circuit depth. For each source index $a$ of this gate, the bound on sources of an individual layer gate gives $a<n+\mathrm{offset}(m)$. The length formula identifies the earlier list's length with $\mathrm{offset}(m)$, so the new position is at or beyond that offset; consequently $a<n+i$.

**Key facts.** `BoolCircuit.GatesAcyclic.nil`, `BoolCircuit.LayeredCircuit.layerGate_args_lt`, `BoolCircuit.LayeredCircuit.length_gatesUpTo`.
