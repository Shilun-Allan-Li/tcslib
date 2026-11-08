<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_verifier_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Padding Verification

**Claim.** If a finite Turing machine decides $L$ within time $a\cdot 2^{n^c}$, then the padding verifier for $L$ at degree $c$ belongs to $\mathrm{P}$.

**Proof.** First replace the given decider by a cleaned-up decider $R$ whose running time is bounded by $B(a2^{n^c}+n+2)$; this is the purpose of the decider-cleaning result (`a3_decider_clean`). Let $F$ be a machine that decodes a pair and returns its first component, running in time $A(|y|+1)$ (`computesFunInTime_pairFst`). Also choose a timed machine $S$ that computes the padding split, running in time $D(|w|+1)^{c+2}$ (`a3_split_timed`).

Use a verifier that first computes the split and then applies a buffered composition of the decoder and cleaned decider, with a nonempty-input wrapper. By the polynomial-time characterization of $\mathrm{P}$ (`mem_P_iff`), it suffices to bound this verifier by a constant times $(|w|+1)^{c+2}$ and show it returns the correct indicator.

Fix an input $w$ and put $P=(|w|+1)^{c+2}$. Since $c+2\ge1$, we have $|w|+1\le P$. If the split finder returns no witness, the split machine outputs the empty word. The nonempty-input wrapper returns false on that empty word, exactly the verifier's indicator in this case. Buffered composition (`a3_comp_at`) gives a running-time bound for these stages; the fixed overhead is absorbed into $K(|w|+1)$ for $K=3A+B(a+3)+10$, and hence into $KP$.

If the split finder returns $n$, let $x$ be the prefix of $w$ of length $n$, let $u$ be the remaining suffix, and let $y$ be their pair encoding. The split specification gives $n\le |w|$ and the equation $n+2^{(n+1)^c}=|w|$ (`a3_split_spec`, with the padding constant specialized to one). The encoding has length at most $2|w|+2$ (`a3_split_length`), and decoding it recovers $x$ as its first component (`pairDecode_pairEncode`). The split-time budget also yields $a2^{n^c}\le a|w|$ (`a3_source_budget`). Thus the decoder costs at most $3A(|w|+1)$, while the cleaned decider costs at most $B(a+3)(|w|+1)$. Adding the composition overhead and the split-machine time gives at most $D P+K(|w|+1)\le(D+K)P$. The output is the indicator of whether $x\in L$, which is precisely the padding verifier's definition in the successful-split case. Therefore this verifier witnesses membership in $\mathrm{P}$.

**Key facts.** `Complexity.a3_decider_clean`, `Turing.FinTM.computesFunInTime_pairFst`, `Complexity.a3_split_timed`, `Complexity.mem_P_iff`, `Complexity.a3_comp_at`, `Complexity.a3_nonempty_nil`, `Complexity.a3_split_spec`, `Complexity.a3_split_length`, `Turing.pairDecode_pairEncode`, `Complexity.a3_source_budget`.
