<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.length_tabFixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the fixed table circuit

**Claim.** For every kind $\kappa_0$, the fixed table circuit has length $\mathrm{tabG}(m,w,F)+w$.

**Proof.** Write $a=\mathrm{kindWidth}(\kappa_0)$ and $T=\mathrm{tabG}(m,w,F)$. The circuit consists of the embedded gadgets, $T-a$ padding gates, and one copy gate for each of the $w$ outputs. The embedded part has length $a$ (`length_embedAll`), and the copy-gate part has length $w$. Since $a\le T$ (`kindWidth_le_tabG`), the padding length is $T-a$. Adding the three lengths gives $a+(T-a)+w=T+w$.

**Key facts.** `BoolCircuit.kindWidth_le_tabG`, `BoolCircuit.length_embedAll`.
