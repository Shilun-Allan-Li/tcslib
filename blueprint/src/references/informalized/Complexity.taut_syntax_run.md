<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_syntax_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete Syntax Pass

**Claim.** If $x$ is a prefix followed by the paired encoding of $a$ and $u$, then after $2|a|+2$ steps the verifier has consumed the prefix and the paired bits of $a$ and the separator, with its work tape empty and head at $0$. It is in certificate-copy state exactly when scanning $a$ from $s$ ends in the exact-end state; otherwise it is in verdict state with bit $1$.

**Proof.** Induct on the word $a$. For the empty word, the two steps read the separator $01$, and the separator transition lemma gives the stated state and configuration. For $a=b::a'$, first rewrite the input as the prefix followed by the pair $bb$ and then the paired encoding of $a'$ and $u$. The two-bit scanning lemma advances the machine across $bb$ and updates its syntax state from $s$ to the state obtained by reading $b$. The run-addition law then splits the total run into these first two steps and the remaining run. Apply the induction hypothesis to $a'$ with the extended prefix and updated state. Since folding over a cons first applies the transition for $b$, the final state has exactly the claimed characterization; the encoding length identity supplies the required input-position bound.

**Key facts.** `Complexity.taut_syntax_separator`, `Complexity.taut_syntax_double`, `Turing.MultiTapeTM.runFrom_add`, `Turing.universal_pair_length`.
