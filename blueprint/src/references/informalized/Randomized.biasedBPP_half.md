<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoin.lean :: Randomized.biasedBPP_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half-Biased BPP Equals BPP

**Claim.** The language class decided in polynomial time using independent fair choice bits with acceptance probability at least $2/3$ is exactly ordinary BPP with the same time and acceptance bounds.

**Proof.** Fix a finite nondeterministic machine, a language, and a time bound. For each input, its acceptance event is the event that the machine outputs the indicator of membership. The fair-bit identity (`Randomized.biasedProb_half`) says that the probability of this event under bias $1/2$ equals the uniform probability used to define ordinary BPP. Casting the rational uniform probability into the reals preserves the comparison with $2/3$, so the two time-bounded decision conditions are equivalent for every machine, language, and time bound. The polynomial-time classes take unions over the same exponents and existentially quantify over the same machine and constant; replacing one equivalent decision condition by the other proves both inclusions and hence equality.

**Key facts.** `Randomized.biasedProb_half`.
