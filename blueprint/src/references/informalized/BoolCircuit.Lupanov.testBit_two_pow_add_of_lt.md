<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LupanovGates.lean :: BoolCircuit.Lupanov.testBit_two_pow_add_of_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Digits After Adding a Power of Two

**Claim.** If $t<2^L$, then digit $r$ of $2^L+t$ is true exactly when digit $r$ of $t$ is true or $r=L$.

**Proof.** Compare $r$ with $L$. Below $L$, adding $2^L$ does not change the lower digits, and the added power contributes no digit there. At $r=L$, the bound $t<2^L$ means that $t$ contributes no digit at position $L$, while the added power contributes one. Above $L$, both $t$ and $2^L+t$ are smaller than $2^r$, so their digits at position $r$ are false. These three cases give the stated disjunction.
