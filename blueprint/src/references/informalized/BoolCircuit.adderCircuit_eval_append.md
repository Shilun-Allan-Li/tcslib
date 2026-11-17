<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Adder.lean :: BoolCircuit.adderCircuit_eval_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adder Circuit Recognizes Addition

**Claim.** For finite Boolean lists $a,b,c$ of equal length, the adder circuit on their concatenation outputs true if and only if the binary integer represented by $c$ equals the sum of those represented by $a$ and $b$.

**Proof.** Let the common block length be $m$. The concatenated input has length $3m$, so its length divided by three is $m$. The circuit evaluation theorem expresses its output as bitwise agreement between the sum of the first two blocks and the third block, together with absence of a final carry (`BoolCircuit.adderCircuit_eval`). The agreement-and-no-carry characterization says that this conjunction is equivalent to equality of the three length-$m$ prefix values, with the third equal to the sum of the first two (`BoolCircuit.agree_and_noCarry_iff`). Each block's binary value is its prefix value over its own length (`BoolCircuit.bitsVal_eq_prefixVal`). Finally, the input bits at offsets $0$, $m$, and $2m$ agree, over the first $m$ positions, with the entries of $a$, $b$, and $c$, respectively. This follows by indexing into the concatenation (`BoolCircuit.RippleCarry.inBits_get`) and using the equal-length assumptions. Prefix values are unchanged when their defining sequences agree throughout the prefix (`BoolCircuit.prefixVal_congr`). Substituting these three block identifications gives precisely the claimed equivalence.

**Key facts.** `BoolCircuit.adderCircuit_eval`, `BoolCircuit.agree_and_noCarry_iff`, `BoolCircuit.bitsVal_eq_prefixVal`, `BoolCircuit.RippleCarry.inBits_get`, `BoolCircuit.prefixVal_congr`.
