<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.certSplit_language -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split Language Characterization

**Claim.** A word $y$ admits a split into a prefix $x$ and suffix $u$ with the prescribed length relation and true output exactly when the split solver returns an index whose corresponding prefix and suffix have true output.

**Proof.** Split according to the solver’s result. If it returns no index, suppose a qualifying decomposition $y=xu$ existed. Its prefix length is at most $|y|$, and the required suffix length makes that prefix length satisfy the solver’s defining equation. Thus the search over indices up to $|y|$ would find a solution, contradicting its returning none. Conversely, no qualifying decomposition can be produced from the right-hand condition, which is false in this case. If the solver returns $i$, its validity lemma (\texttt{Turing.certSplit\_valid}) says that the suffix after the first $i$ bits has exactly the required length relative to the prefix. Given any qualifying decomposition $y=xu$, the split-uniqueness lemma (\texttt{Turing.append\_split\_unique}) applies: the function $n\mapsto n+C(n+1)^c$ is strictly increasing (\texttt{Turing.certificateLength\_strictMono}), so two decompositions of the same word whose suffix lengths follow this rule must have equal prefixes and equal suffixes. The given decomposition is therefore the solver’s prefix and suffix, and its true-output condition is the stated condition. In the other direction, take the prefix and suffix of $y$ at index $i$. They concatenate to $y$, their length relation follows from the solver-validity lemma, and the assumed output condition supplies the required true output.

**Key facts.** `Turing.certSplit_valid`, `Turing.certificateLength_strictMono`, `Turing.append_split_unique`.
