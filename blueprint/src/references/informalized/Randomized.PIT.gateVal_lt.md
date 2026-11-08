<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZeroPEval.lean :: Randomized.PIT.gateVal_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Gate Values Are Bounded by the Modulus

**Claim.** For positive modulus $k$, the value of any arithmetic gate computed modulo $k$ is strictly less than $k$.

**Proof.** Split according to the gate constructor. In each case—an input variable, the constant one, addition, subtraction, or multiplication—the definition of the gate value is a natural number reduced modulo $k$. Since $k>0$, the remainder theorem gives a result strictly below $k.
