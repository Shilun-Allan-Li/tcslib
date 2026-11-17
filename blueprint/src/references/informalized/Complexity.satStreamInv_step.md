<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satStreamInv_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of the encoded invariant

**Claim.** For every finite binary string $x$ and word $w$, if $w$ satisfies the encoded loop invariant on $x$, then the encoded next-state word also satisfies that invariant.

**Proof.** Unpack the invariant to obtain a state $s$ such that $w$ is its encoding and $s$ satisfies the bound for $x$. The round-trip lemma for state encodings says that reading the encoding of $s$ recovers exactly $s$. Thus the next-state word is the encoding of the state produced by one round from $s$. The round-bound lemma shows that this resulting state still satisfies the required bound. It witnesses the invariant for the next-state word.

**Key facts.** `Complexity.satStreamRead_word`, `Complexity.satStreamRound_bound`.
