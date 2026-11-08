<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_runWith_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Turing Machine Choice Splits Run Probability

**Claim.** When the two possible first choice bits send a Turing machine from configuration $C$ to $C_1$ and $C_0$, respectively, the probability of a configuration property after $T+1$ random bits is the average of its probabilities after $T$ bits from those two successors.

**Proof.** Fix the first bit $c$. The run equation says that running on the word $c$ followed by the remaining $T$ bits is the same as first taking the step selected by $c$ and then running those remaining bits. By the assumed successor equations, these are runs from $C_1$ when $c=1$ and from $C_0$ when $c=0$; hence the corresponding event probabilities agree (`Turing.NDTM.runWith_cons`, `randProb_congr`). The first bit is uniformly distributed, so averaging the two conditional probabilities gives the length-$(T+1)$ probability (`randProb_succ`).

**Key facts.** `Randomized.randProb_congr`, `Randomized.randProb_succ`, `Turing.NDTM.runWith_cons`.
