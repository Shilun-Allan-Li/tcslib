<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedCut_StateTape_end -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# End of the Unary State Encoding

**Claim.** For every natural number $n$, the unary state tape encoding $n$ is blank at cell $n+1$.

**Proof.** The tape is the finite word consisting of an initial false symbol followed by $n$ true symbols. Its length is therefore $n+1$, so the list has no entry at index $n+1$. Since this cell is nonnegative, the tape lookup returns the option value `none`.
