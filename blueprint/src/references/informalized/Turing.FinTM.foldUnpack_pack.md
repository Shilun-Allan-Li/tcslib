<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldUnpack_pack -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unpacking Reverses Packing

**Claim.** For every alphabet $\Gamma$ and folded-alphabet symbol $v$, unpacking its canonical packing returns $v$.

**Proof.** Write $v$ as its origin flag and its two optional tape entries. Packing returns that symbol except in the unique blank case, where it returns absence; unpacking absence supplies precisely the blank symbol. In every other case packing returns the symbol itself, which unpacking preserves. Thus unpacking the packed value returns $v$.
