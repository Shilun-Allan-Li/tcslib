<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.length_tabProgGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the generated gate list

**Claim.** For every starting index $i$ and finite instruction list $prog$, the generated gate list has length $(m+\mathrm{tabG}(m,w,F)+w)|prog|$.

**Proof.** Induct on the instruction list, allowing the starting index to vary. For the empty list, no gates are generated. For a list beginning with instruction $ins$, the construction concatenates the gates for that instruction with the gates generated from the remaining instructions at the next index. The first part has length $\mathrm{tabW}(m,w,F)$ (`length_tabInstrGates`), and the induction hypothesis gives the remaining part length $\mathrm{tabW}(m,w,F)|prog|$. Their sum is $\mathrm{tabW}(m,w,F)(|prog|+1)$, which is the desired formula.

**Key facts.** `BoolCircuit.length_tabInstrGates`.
