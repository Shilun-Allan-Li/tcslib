<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.length_tabInstrGates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of an instruction gate list

**Claim.** For every index and instruction, the generated instruction gate list has length $\mathrm{tabW}(m,w,F)=m+\mathrm{tabG}(m,w,F)+w$.

**Proof.** The instruction list concatenates $m$ copy gates, one for each padded source, with the fixed table circuit shifted to the instruction's position. Shifting gates does not change the list length. The fixed table circuit has length $\mathrm{tabG}(m,w,F)+w$ (`length_tabFixed`), so the total length is $m+\mathrm{tabG}(m,w,F)+w$, as claimed.

**Key facts.** `BoolCircuit.length_tabFixed`.
