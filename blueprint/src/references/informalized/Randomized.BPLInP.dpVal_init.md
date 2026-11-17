<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPCount.lean :: Randomized.BPLInP.dpVal_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial dynamic-programming value

**Claim.** If every choice string of some length makes the machine halt, then the depth-$V$ dynamic-programming value at the initial configuration code equals $2^V$ times the probability that the machine outputs exactly $[1]$ on a uniform choice string of length $V$.

**Proof.** Apply the depth-$t$ probability identity (`dpVal_eq`) with $t=V$ and with no choices fixed in advance. Running the empty word leaves the initial configuration unchanged (`runWith_nil`), so the left side is the depth-$V$ value at the initial code. The identity expresses it as $2^V$ times the probability that the length-$V$ run is halted and has output $[1]$. The code-bound halting lemma (`haltsWithin_of_codes`) upgrades the assumed halting guarantee at length $T$ to one at length $V$. Consequently every outcome in this probability experiment is halted, and the event “halted and output $[1]$” is equivalent, on every sampled choice string, to “output $[1]$.” Equality of these events preserves their probabilities (`randProb_congr`), and the latter probability is the machine's output probability by definition.

**Key facts.** `Randomized.BPLInP.dpVal_eq`, `Turing.NDTM.runWith_nil`, `Randomized.BPLInP.haltsWithin_of_codes`, `Randomized.randProb_congr`.
