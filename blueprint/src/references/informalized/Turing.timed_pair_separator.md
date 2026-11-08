<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_pair_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Separator Positions

**Claim.** In the encoding formed by doubling each bit of $\alpha$, then appending $01$ and $x$, the bits at positions $2|\alpha|$ and $2|\alpha|+1$ are respectively $0$ and $1$.

**Proof.** Induct on $\alpha$. For the empty word, the encoding begins with the separator $01$, so the claim holds at positions zero and one. When $\alpha=b::\alpha_0$, the encoding begins with the doubled bit $bb$; removing those two entries leaves the encoding built from $\alpha_0$. The separator positions for $\alpha$ are exactly two positions after the corresponding separator positions for $\alpha_0$, so the induction hypothesis gives the desired bits.
