<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.char_s_zero_vec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Character at the Zero Vector

**Claim.** For every index vector $s$, the Fourier character $cc_s$ takes the value $1$ at the zero vector.

**Proof.** At the zero vector, every term $s_i\cdot 0_i$ in the dot product vanishes, so the dot product is $0$ (`zkDot_zero_right`). The character is therefore the root-of-unity map evaluated at $0$, which equals $1$ (`toOmega_zero`).

**Key facts.** `ZkFourier.zkDot_zero_right`, `ZkFourier.toOmega_zero`.
