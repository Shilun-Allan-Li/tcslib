<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.bpp_error_reduction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplification of Weak Randomized Decision

**Claim.** If a language has an efficient verifier whose acceptance probability on members and rejection probability on nonmembers are each at least $1/2+\min\{1/6,(|x|+1)^{-c}\}$, and the verifier model is closed under majority amplification, then for every $d$ it has an efficient verifier whose corresponding probabilities are each at least $1-2^{-((|x|+1)^d+1)}$.

**Proof.** Choose a weak verifier $M$ with randomness length $q=a(n+1)^k$, where $n=|x|$. Run it independently on $K=56(n+1)^{2c+d}$ consecutive blocks, and accept when more than half the votes accept. Closure under majority amplification makes this new verifier efficient; its total randomness length is $Kq=(56a)(n+1)^{2c+d+k}$. The weak advantage is positive (`Randomized.weakAdv_pos`). Also, for each input, accepting and rejecting single-run probabilities sum to one (`Randomized.randProb_bool_false`), and a Boolean output's negation has the same probability as rejection (`Randomized.randProb_congr`).

For a member $x$, the probability a run rejects is at most $1/2-\varepsilon$, where $\varepsilon$ is the weak advantage. Failure of the majority verifier is exactly the event that at least half the blocks reject: complementary vote counts sum to $K$, so this event is equivalent to $K\le 2$ times the number of rejecting votes. Applying the majority tail bound to rejecting votes gives probability at most $2(1-4\varepsilon^2)^{\lfloor K/2\rfloor}$ (`Randomized.randProb_tail_le`). The chosen value of $K$ makes this at most $2^{-((n+1)^d+1)}$ (`Randomized.weakAdv_tail_bound`), so acceptance probability is at least one minus that quantity (`Randomized.randProb_not`).

For a nonmember, the acceptance probability of one run is at most $1/2-\varepsilon$. The same tail bound controls the event that at least half the votes accept. Failure to reject by majority implies this event, so monotonicity of probability bounds the failure probability by the same tail estimate (`Randomized.randProb_mono`). The estimate again gives error at most $2^{-((n+1)^d+1)}$, establishing the rejection guarantee.

**Key facts.** `Randomized.weakAdv_pos`, `Randomized.randProb_bool_false`, `Randomized.randProb_congr`, `Randomized.randProb_tail_le`, `Randomized.weakAdv_tail_bound`, `Randomized.randProb_not`, `Randomized.randProb_mono`.
