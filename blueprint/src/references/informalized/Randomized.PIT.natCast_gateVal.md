<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.natCast_gateVal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate evaluation modulo an integer

**Claim.** When every entry of $v$ is less than $k$, the natural-number value of any arithmetic gate, reduced modulo $k$, equals its evaluation in $\mathbb Z/k\mathbb Z$ on the corresponding reduced inputs and prior values.

**Proof.** Check the gate forms. For a variable and for the constant one, reducing the defining natural value gives the corresponding ring input or unit. For addition and multiplication, casting the modular sum or product into the quotient ring gives the sum or product of the cast operands; the prior list entries are identified with their casts by `Randomized.PIT.getD_map_natCast`. For subtraction, the natural definition uses $x+(k-y)$ modulo $k$. The bound on entries of $v$ ensures each selected prior value $y$ is at most $k$, by `Randomized.PIT.getD_le`; consequently $k-y$ casts to the additive inverse of $y$ in $\mathbb Z/k\mathbb Z$. The expression therefore equals $x-y$, as required. The same lookup identity supplies the cast prior values in each arithmetic case.

**Key facts.** `Randomized.PIT.getD_map_natCast`, `Randomized.PIT.getD_le`.
