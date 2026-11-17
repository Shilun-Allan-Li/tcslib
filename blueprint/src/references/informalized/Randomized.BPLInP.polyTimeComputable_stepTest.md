<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.polyTimeComputable_stepTest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Step Test

**Claim.** For every finite-state nondeterministic Turing machine $N$ over the binary alphabet, natural numbers $c,B,e$, and bit $b$, the function mapping $z$ to the one-bit string containing the step test for $N$, choice $b$, and input $z$ is polynomial-time computable.

**Proof.** The step language is in logarithmic space (\texttt{stepLang\_mem}), so its one-bit indicator is polynomial-time computable by the logspace-indicator result (\texttt{polyTimeComputable\_indicator\_of\_LOGSPACE}). The test first decodes selected components of $z$ using the first- and second-component decoding functions; these are polynomial-time computable (\texttt{polyTimeComputable\_pairFstD} and \texttt{polyTimeComputable\_pairSndD}). It then assembles those components into the nested paired encoding required by the step language. Pair encoding preserves polynomial-time computability (\texttt{PolyTimeComputable.pairEncode}), and composition preserves it as well. Composing this preprocessing with the indicator therefore computes the step test in polynomial time.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.Codec.stepLang_mem`, `Randomized.BPLInP.polyTimeComputable_indicator_of_LOGSPACE`, `Complexity.PolyTimeComputable.pairEncode`.
