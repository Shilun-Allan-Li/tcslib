<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Adleman.lean :: Randomized.adleman -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized to polynomial size

**Claim.** Under the stated majority-closure, bounded-error verification, and polynomial circuit-simulation hypotheses, $L$ is decidable by a family of fan-in-two circuits of polynomial size.

**Proof.** First amplify the verifier’s error using majority closure. The error-reduction result (`Randomized.bpp_error_reduction`), after converting the given BPP verifier to the weak form (`Randomized.inBPPWeak_iff_inBPP`), supplies an efficient verifier whose error on each input of length $n$ is at most $2^{-(n+2)}$.

Fix $n$. For each input $v\in\{0,1\}^n$, call a random string bad if the amplified verifier gives the wrong answer on $v$. The error guarantee bounds the fraction of bad strings for this input by $2^{-(n+2)}$: the proof treats members and nonmembers separately, replacing the wrong-answer event by the complement of the corresponding correct-answer event. The identities for complementary probabilities and for predicates that agree on every random string justify these replacements (`Randomized.randProb_not`, `Randomized.randProb_congr`).

There are $2^n$ inputs of length $n$. If every random string were bad for at least one input, the union of all input-specific bad sets would cover the $2^m$ random strings, where $m$ is the verifier’s random-bit count. But the union has size at most the sum of the individual sizes, hence at most $2^n 2^{-(n+2)}2^m=2^m/4$, a contradiction. Here the number of Boolean strings of length $j$ is $2^j$ (`Randomized.card_univ_bitstrings`), and the union bound is applied to the finite sets of bad strings. Thus for each $n$ one can fix a single random string that makes the verifier correct on every length-$n$ input.

The circuit-simulation hypothesis now gives, at each length, a fan-in-two circuit of polynomial size computing the verifier with that fixed random string. Use these circuits as the family. On any word $w$, its circuit output equals the verifier’s answer on $w$ and the chosen string for length $|w|$; the simultaneous correctness property makes that output true exactly when $w\in L$. The circuit family therefore decides $L$ and has polynomial size.

**Key facts.** `Randomized.inBPPWeak_iff_inBPP`, `Randomized.bpp_error_reduction`, `Randomized.randProb_congr`, `Randomized.randProb_not`, `Randomized.card_univ_bitstrings`, `BoolCircuit.DAGCircuitFamily.mem_language_iff`.
