<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEvalCfg_work -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Certificate Symbol Under the Last Head

**Claim.** In the canonical evaluation configuration, the symbol under the evaluator's last work-tape head is the certificate buffer's content at offset $j$.

**Proof.** The last tape among the evaluator's $k+1$ work tapes is the added tape: its index is not less than $k$. By the definition of the canonical configuration, that tape stores the buffer tape built from $u$, and its head is at offset $j$. Evaluating the work-tape symbol at the head therefore gives exactly the buffer's content at $j$.
