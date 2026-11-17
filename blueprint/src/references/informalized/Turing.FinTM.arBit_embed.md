<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arBit_embed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bit decoding on embedded bits

**Claim.** For an embedding $e:\{0,1\}\hookrightarrow\Gamma$, the decoder that returns true exactly on $e(1)$ sends each embedded bit $e(b)$ back to $b$.

**Proof.** There are two cases. If $b$ is true, then $e(b)=e(1)$, so the decoder's equality test is true. If $b$ is false, then $e(b)\ne e(1)$: injectivity of $e$ would otherwise imply $b=1$. Thus the decoder returns false in this case, as required.
