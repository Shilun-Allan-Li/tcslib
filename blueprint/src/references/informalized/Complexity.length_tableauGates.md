<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyTableau.lean :: Complexity.length_tableauGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tableau gate-list length

**Claim.** For every finite-state Turing machine $M$ with Boolean input alphabet and every $n,t\in\mathbb{N}$, the gate list at time $t$ in the tableau construction has length $2+tW$, where $W$ is the total width of the tableau gadgets.

**Proof.** Induct on $t$. At time zero the gate list consists of the two initial constant gates, so its length is $2$. For the successor step, the construction appends one embedded copy of each tableau gadget to the previous gate list. By the definition of total gadget width, these appended gates have total length $W$. Thus the new length is the previous length plus $W$; using the induction hypothesis gives $2+tW+W=2+(t+1)W$.
