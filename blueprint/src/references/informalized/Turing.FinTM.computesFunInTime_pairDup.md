<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairDup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duplicating a Word in Pair Encoding

**Claim.** A finite Turing machine outputs the pair encoding of $(x,x)$, with each bit doubled, then the separator $01$, then $x$, in time bounded by a constant multiple of the input length plus one.

**Proof.** Take the machine `pairDupTM` and set $c=4$. The computation theorem `pairDup_computes` states that on each input $x$ this machine outputs precisely the pair encoding of $(x,x)$ and halts within $4(|x|+1)$ steps. This gives the claimed uniform bound.

**Key facts.** `Turing.FinTM.pairDup_computes`.
