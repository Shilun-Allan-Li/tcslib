<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitter.lean :: Complexity.UTab.flatMap_exec_sgOps -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary output of gate instructions

**Claim.** Executing the instruction sequence that prints a one, encodes a gate kind, prints each argument's unary value between delimiter bits, and ends with zero produces one followed by the encoding of the gate with the evaluated argument values.

**Proof.** For each linear expression $a$, the instructions that print a one, execute its linear-expression operations, and print zero produce one followed by the unary encoding of $a$'s value. Indeed, the register-printing operations contribute one for each register value in the expression, while its constant term contributes that many additional ones; the false bit terminates this unary numeral. The gate-kind operations print exactly the gate-kind encoding, by \texttt{flatMap\_exec\_bitsOps}. Applying the linear-expression observation to each argument in order, the argument-list encoding identity \texttt{encodeList\_eq\_flatMap} assembles these delimited unary numerals into the gate's argument encoding. The initial one and the final zero then give precisely one followed by the encoding of the gate with the evaluated arguments.

**Key facts.** `Complexity.CounterProg.flatMap_exec_linOps`, `Complexity.CounterProg.flatMap_exec_bitsOps`, `Complexity.UTab.encodeList_eq_flatMap`.
