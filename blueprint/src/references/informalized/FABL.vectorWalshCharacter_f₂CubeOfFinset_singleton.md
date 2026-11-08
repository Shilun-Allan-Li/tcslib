<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.vectorWalshCharacter_f₂CubeOfFinset_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character at a Singleton Frequency

**Claim.** For a coordinate $i$ and $x\in\mathbb{F}_2^n$, the Walsh character indexed by the vector that is $1$ at $i$ and $0$ elsewhere equals the binary sign of $x_i$.

**Proof.** The support of the frequency vector that is $1$ at $i$ and $0$ elsewhere is exactly the singleton $\{i\}$; this follows from the inverse property of the correspondence between cube vectors and coordinate subsets (`f₂CubeEquivFinset`). The character definition then reduces its coordinate sum over that singleton to $x_i$. Applying the binary sign gives the asserted value.
