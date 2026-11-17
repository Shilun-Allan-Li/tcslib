<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.compl_mem_ZTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement Closure

**Claim.** For every time bound $T$ and Boolean-string language $L$, if $L$ belongs to $\mathrm{ZTIME}(T)$, then its complement does as well.

**Proof.** Choose a constant $c$ and a randomized machine $N$ witnessing that $L$ belongs to $\mathrm{ZTIME}(T)$. Keep the same machine and flip its output. The output-flipping result says that this machine decides $L^c$ within the same time bound (Turing.FinNDTM.ZDecidesInTime.flipOutput). Thus the same $c$ and the flipped machine witness $L^c\in\mathrm{ZTIME}(T)$.

**Key facts.** `Turing.FinNDTM.ZDecidesInTime.flipOutput`.
