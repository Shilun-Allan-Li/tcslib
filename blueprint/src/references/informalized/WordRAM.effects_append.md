<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.effects_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Instruction Effects

**Claim.** Applying the concatenated instruction list $l_1 ++ l_2$ to memory $m$ has the same effect as applying $l_1$ first and then $l_2$.

**Proof.** The effect of a list is defined by folding through its instructions from left to right, feeding each resulting memory into the next instruction’s effect. Folding over a concatenation first processes all of $l_1$, producing the memory $\mathrm{effects}(l_1,m)$, and then processes $l_2$ starting from that memory. This is the asserted identity.
