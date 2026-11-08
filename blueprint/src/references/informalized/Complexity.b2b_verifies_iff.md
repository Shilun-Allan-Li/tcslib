<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_verifies_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-Witness Characterization

**Claim.** An integer in the range $0\le r\le 2^Q-1$ whose width-$Q$ little-endian binary word appended to $x$ lies in $V$ exists exactly when some length-$Q$ Boolean word appended to $x$ lies in $V$.

**Proof.** For the forward direction, take the witness $r$ and use its enumerated width-$Q$ word. The length theorem for enumerated words (`Complexity.Meyer.length_enumWord`) gives length $Q$, and membership is the assumed one.

Conversely, suppose $u$ has length $Q$ and $x\mathbin{++}u\in V$. Choose the integer value of $u$ (`Complexity.Meyer.ctrVal_lt`). Its value is strictly less than $2^{|u|}$, hence at most $2^Q-1$. The encoding identity (`Complexity.Meyer.enumWord_ctrVal`) says that the width-$Q$ word enumerated from this value is exactly $u$. Substituting that identity into the assumed membership proves the required witness statement.

**Key facts.** `Complexity.Meyer.length_enumWord`, `Complexity.Meyer.ctrVal_lt`, `Complexity.Meyer.enumWord_ctrVal`.
