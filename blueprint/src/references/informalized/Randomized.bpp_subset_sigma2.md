<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SipserGacs.lean :: Randomized.bpp_subset_sigma2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Lies in the Second Existential Level

**Claim.** If the verifier model is closed under polynomial majority amplification and under the specified shift-or verifier, then every language in BPP for that model has a two-witness characterization: membership is equivalent to the existence of a polynomial-length word $u$ such that every polynomial-length word $v$ makes the two-witness verifier accept.

**Proof.** 1. Start with the BPP verifier and its polynomial random-string length. Apply concrete majority amplification (`amplify_concrete`) with the chosen parameters. The resulting efficient verifier has error at most $2^{-T}$, where $T$ is a polynomially bounded repetition parameter. Set $m$ to its random-string length and $k_s$ to the number of shifts. The displayed polynomial choices ensure both $m<Tk_s$ and $k_s<2^T$; the latter follows from the shift-count bound (`shift_count_lt_two_pow`). Closure under shift-or gives efficiency of the eventual two-witness verifier (`hShift`).

2. For a yes-instance, regard a candidate $u$ as $k_s$ consecutive blocks of $m$ bits. For each possible $m$-bit word $v$, xor it with each block and run the amplified verifier. We show some $u$ makes at least one run accept for every $v$. Fix $v$ temporarily and choose $u$ uniformly. Each block is uniform, and the block-count distribution theorem (`randProb_blockCount`) says the probability that all $k_s$ runs reject is at most $2^{-Tk_s}$. Thus the number of bad $u$ for this fixed $v$ is at most $2^{-Tk_s}2^{k_sm}$. Taking the union over all $2^m$ choices of $v$, the total number of bad words is strictly less than $2^{k_sm}$, because $m<Tk_s$. Hence a suitable $u$ exists. Its length is exactly $k_sm$, as required by the chosen polynomial witness bound. Any length-$m$ word $v$ can be represented by a function on the finite index set, and a positive block count gives an accepting shift; therefore the shift-or verifier accepts.

3. For a no-instance, fix any candidate $u$. For each shift block, xor with a uniformly random $v$ preserves the uniform distribution (`randProb_xor_left`), so the probability that that shift accepts is at most $2^{-T}$. A union bound over the $k_s$ shifts, together with $k_s<2^T$, shows that fewer than all $2^m$ choices of $v$ cause any shift to accept. The count of Boolean functions on an $m$-element set is $2^m$ (`card_univ_bitstrings`), so the strict cardinality bound gives a $v$ for which every shift rejects (`exists_notMem_of_card_lt`). The stipulated universal acceptance therefore cannot hold. This proves the reverse implication and the two-witness characterization.

**Key facts.** `Randomized.amplify_concrete`, `Randomized.shift_count_lt_two_pow`, `Randomized.randProb_blockCount`, `Randomized.randProb_xor_right`, `Randomized.card_univ_bitstrings`, `Randomized.exists_notMem_of_card_lt`, `Randomized.randProb_xor_left`, `Randomized.exists_ofFn_eq`.
