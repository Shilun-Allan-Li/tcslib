<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.cfgTab_encode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Configuration tableau encoding

**Claim.** The Boolean encoding of the configuration-tableau circuit consists of the input prefix, the encoded preamble, the encodings of the tableau instructions in order, and the final output encoding whose unary length is the designated linear expression evaluated at time $T+1$.

**Proof.** By the definition of circuit encoding, the circuit contributes the unary encoding of its number of inputs, followed by the list encoding of its gates and the unary encoding of its output index. The list-encoding identity (\texttt{encodeList\_eq\_gbits}) turns the gate-list portion into the concatenation of the prefixed gate encodings, terminated by zero. The tableau circuit's gates split into the preamble and the instruction-program gates; the encoding respects this concatenation by \texttt{gbits\_append}. The preamble is exactly the two constant gates, one constant gate for each bit of $z$, and the prescribed false constant gates. The program is the range of tableau instructions indexed from zero to $(T+1)\operatorname{Str}(M,n,z,T)-1$; the range-expansion fact \texttt{tabProgGates\_range'} identifies its gate list with the concatenation of the corresponding instruction gate lists, in order. Finally, \texttt{cfgTab\_output} identifies the circuit's output index with the stated linear expression at the register values for time $T+1$ and loop counter zero. Expanding the unary encoding of that index gives the final zero, that many ones, and a terminating zero, as claimed.

**Key facts.** `Complexity.UTab.encodeList_eq_gbits`, `Complexity.UTab.gbits_append`, `Complexity.UTab.tabProgGates_range'`, `Complexity.UTab.cfgTab_output`.
