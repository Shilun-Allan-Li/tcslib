<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauCircuit.lean :: BoolCircuit.runWith_tabPre -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Tabulation Preamble

**Claim.** Evaluating the tabulation preamble from $x$ appends $[false,true]$, the entries of $z$, and $W$ copies of $false$.

**Proof.** The preamble is exactly the list of constant gates obtained by mapping `constGate` over the Boolean list $[false,true]++z++\operatorname{replicate}(W,false)$. The constant-gate evaluation formula (`runWith_eval_constGates`) says that evaluating such a mapped list appends the original Boolean list to the initial list. Taking the initial list to be $x$ gives the stated result.

**Key facts.** `BoolCircuit.runWith_eval_constGates`.
