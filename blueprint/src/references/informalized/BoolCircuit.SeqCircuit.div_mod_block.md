<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/SequentialCircuit.lean :: BoolCircuit.SeqCircuit.div_mod_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quotient and Remainder Within a Block

**Claim.** If $m<S$, dividing $Sk+m$ by $S$ gives quotient $k$ and remainder $m$.

**Proof.** The bound $m<S$ implies $S>0$. For the quotient, the product-plus-remainder division rule gives $(Sk+m)/S=(Sk)/S+m/S=k+0=k$. For the remainder, the corresponding modular rule gives $(Sk+m)\%S=((Sk)\%S+m)\%S=m$, since the product is divisible by $S$ and $m<S$.
