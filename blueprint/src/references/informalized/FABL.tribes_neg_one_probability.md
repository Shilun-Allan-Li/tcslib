<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribes_neg_one_probability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Negative tribes probability

**Claim.** Under uniform input, the probability that $\mathrm{Tribes}_{w,s}(x)=-1$ is $1-(1-2^{-w})^s$.

**Proof.** Count the inputs on which tribes equals $+1$, then take the complementary probability. A width-$w$ block has $2^w$ possible sign assignments, and exactly one of them has AND value $-1$ (the assignment with every sign equal to $-1$). Thus there are $2^w-1$ assignments making its AND value $+1$. Reindexing the full input by its $s$ blocks is a bijection, so the number of inputs for which every block has AND value $+1$, equivalently tribes has value $+1$, is $(2^w-1)^s$. The full cube has $2^{sw}$ inputs, and hence the probability of tribes being $+1$ is $(2^w-1)^s/2^{sw}=(1-2^{-w})^s$. The two sign-valued outcomes have probabilities summing to one (the sign partition identity, `FABL.uniformProbability_one_add_neg_one_eq_one`), so the probability of value $-1$ is the stated complement.

**Key facts.** `FABL.uniformProbability_one_add_neg_one_eq_one`.
