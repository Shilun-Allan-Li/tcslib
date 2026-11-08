<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/KarpLipton.lean :: Complexity.PiP_two_subset_SigmaP_two_of_NP_subset_PPoly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second-Level Collapse from Circuits

**Claim.** If every language in NP is decidable by a family of fan-in-two Boolean circuits of polynomially bounded size, then every language in $\Pi_2^P$ belongs to $\Sigma_2^P$.

**Proof.** Take $L\in\Pi_2^P$. Its quantified characterization gives a polynomial-time language $V$ and a condition saying that for each polynomial-length string $u$, there is a polynomial-length string $v$ for which the twice-paired input belongs to $V$ (\texttt{mem\_PiP\_two\_iff\_forall\_exists}). The proof constructs an NP language encoding the relevant prefix condition (\texttt{prefixLang\_mem\_NP}) and applies the circuit hypothesis to obtain a fan-in-two circuit family deciding it. For each input $x$, encode the circuit for the prescribed input length, pad that encoding to the fixed polynomial witness length, and append a marker. The circuit encoding estimate ensures the padded string fits the chosen polynomial bound (\texttt{length\_encode\_le}). The inner language is in coNP (\texttt{innerLang\_mem\_coNP}); the circuit's correctness implies that this encoded witness belongs to it whenever $x\in L$ (\texttt{allGood\_of\_decides}). Conversely, membership of the encoding in the inner language guarantees the required existential witness for every allowed universal string (\texttt{exists\_witness\_of\_allGood}). Thus membership in $L$ is equivalent to the existence of a polynomial-length witness whose pair encoding belongs to a coNP language. The second-level Sigma characterization now gives $L\in\Sigma_2^P$ (\texttt{mem\_SigmaP\_two\_iff}).

**Key facts.** `Complexity.mem_PiP_two_iff_forall_exists`, `Complexity.KarpLipton.prefixLang_mem_NP`, `Complexity.KarpLipton.innerLang_mem_coNP`, `Complexity.KarpLipton.length_encode_le`, `Complexity.KarpLipton.allGood_of_decides`, `Complexity.KarpLipton.exists_witness_of_allGood`, `Complexity.mem_SigmaP_two_iff`.
