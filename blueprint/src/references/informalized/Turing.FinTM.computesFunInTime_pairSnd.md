<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairSnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-component extraction in linear time

**Claim.** A finite Boolean-alphabet Turing machine extracts the second component returned by the pair parser, returning the empty word when parsing fails, in time bounded by a constant times the input length plus one.

**Proof.** Use the machine that extracts the second component, with time bound $5(|x|+1)$. Its computation theorem says that on a valid parse $(a,b)$ it outputs the concatenation of the selected components; choosing the first-component flag false and the second-component flag true makes this exactly $b$. On a failed parse it outputs the empty word. Splitting on the parser result identifies these outputs with the specified function. Take $c=5$.

**Key facts.** `Turing.FinTM.pairExtractTM_computes`.
