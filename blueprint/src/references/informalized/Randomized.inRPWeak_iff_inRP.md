<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.inRPWeak_iff_inRP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weak and Standard One-Sided Recognition

**Claim.** If efficient verifiers in $E$ are closed under the specified disjunction of polynomially many random-tape tests, then for every $c$ and language $L$, weak one-sided recognition is equivalent to standard one-sided randomized recognition.

**Proof.** Starting from weak recognition, apply the one-sided error-reduction theorem with repetition parameter $d=0$. Its closure hypothesis is exactly the assumed closure of $E$ under the verifier that accepts if any of the polynomially many tests accepts. This yields strong one-sided recognition, which implies standard RP recognition. Conversely, standard RP recognition implies the weak condition: its acceptance probability is at least $2/3$, hence at least the minimum of $2/3$ and $(|x|+1)^{-c}$, while its perfect rejection guarantee is unchanged.

**Key facts.** `Randomized.rp_error_reduction`, `Randomized.InRPStrong.toInRP`, `Randomized.InRP.toInRPWeak`.
