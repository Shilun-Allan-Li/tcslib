<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterMain.lean :: Complexity.UTab.goes_rN -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary input scan

**Claim.** If $w=pre ++ (1^a ++ rest)$, then starting at $rN$ with register record $e$, input position $|pre|$, and any prior output, the counter program returns to $rN$ with the input-count register increased by $a$, position $|pre|+a$, and the $a$ ones appended to the output, in at most $3a$ steps.

**Proof.** Proceed by induction on $a$, allowing the prefix and register record to vary. If $a=0$, the initial and final configurations agree, and no output is appended, so the run has length zero.

For the successor case, the next unread input symbol is true because it is the first of the $a+1$ repeated ones. The program reads it and moves from $rN$ to the increment label; it then increments the input-count register and prints one true bit, returning to $rN$. These three instructions consume one input symbol, increase the count by one, and append one true bit. Apply the induction hypothesis to the remaining $a$ ones, with the prefix extended by this first one and the register record already incremented. Concatenating the one-symbol run and the inductive run gives the required final register record, position, and appended list. The first part costs three steps and the remainder at most $3a$, hence the total is at most $3(a+1)$ (`Goes.trans`). The output and register updates are exactly those described by the instruction-step facts; `Goes.congr` aligns the intermediate register records, positions, outputs, and bounds.

**Key facts.** `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.goes_rd_true`, `Complexity.UTab.goes_incR`, `Complexity.CounterProg.goes_out`, `Complexity.CounterProg.goes_refl`, `Complexity.CounterProg.Goes.congr`.
