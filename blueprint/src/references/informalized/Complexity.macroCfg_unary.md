<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Unary Tape Symbol in a Macrostep Configuration

**Claim.** In the macrostep configuration built from $c$ with unary-counter head position $u$, the symbol scanned on that tape is the content of $c$’s unary-counter tape at position $u$.

**Proof.** The scanned symbol is the unary-counter tape’s contents evaluated at the macrostep configuration’s head position. By definition, the macrostep construction retains the base tape contents and assigns the unary-counter head the position $u$. Evaluating those contents at that position gives the stated value.
