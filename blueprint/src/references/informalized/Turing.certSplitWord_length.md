<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certSplitWord_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate Word Length Bound

**Claim.** The certificate word constructed from a bit string $y$ has length at most $2|y|+2$.

**Proof.** If the split solver returns an index $i$, the encoded word has length $2|y_{<i}|+2+|y_{\ge i}|$, by the length formula for the self-delimiting pair encoding (\texttt{Turing.length\_pairEncode}). The prefix and suffix lengths sum to $|y|$, so this is at most $2|y|+2$. If the solver returns no index, the constructed word is empty and the bound is immediate.

**Key facts.** `Turing.length_pairEncode`.
