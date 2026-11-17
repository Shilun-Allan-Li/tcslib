<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Advice.lean :: Complexity.ao_halt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting and Output of the Advice Machine

**Claim.** If the machine's transition on the bit at position $i$ is the action that emits $b$ and halts, then one step from the specified configuration halts and outputs $[b]$.

**Proof.** The one-step transition lemma identifies the machine's step from the configuration at head position $i+1$ with the action prescribed by its transition rule on the bit $w[i]$ (\texttt{Complexity.ao_step}). Since that bit is $v$ and the prescribed action is the halting action emitting $b$, the resulting configuration has state none and appends the one-bit output $[b]$, as required.

**Key facts.** `Complexity.ao_step`.
