<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/Examples.lean :: Complexity.PAL_mem_DTIME_linear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linear-Time Palindrome Decider

**Claim.** The language of binary words equal to their reversals is decidable by a finite deterministic multi-tape Turing machine in at most $3(n+1)$ steps on inputs of length $n$.

**Proof.** Fix an input word $x$ of length $n$. The machine first copies the input to a work tape in $n+1$ steps, returns the relevant head to its starting position in another $n+1$ steps, and enters its comparison phase. The lemmas `pal_copy`, `pal_copy_end`, `pal_rewind`, and `pal_test_start`, together with the run composition identities `runFrom_succ_eq_step'` and `runFrom_add`, identify the configuration after these first $2(n+1)$ steps as the start of the test, with the two heads positioned to compare corresponding symbols. The test then takes $n+1$ steps, as recorded by `pal_test`. Its output is the single bit indicating whether every compared pair matches. More precisely, `palMatches x 0` is equivalent to $x$ being a palindrome: equality of the word with its reversal makes the corresponding entries equal, and conversely equality at every index gives equality of the lists by extensionality. Since $2(n+1)+(n+1)=3(n+1)$, the machine halts at the stated time and outputs $1$ exactly on palindromes, establishing the claimed deterministic time bound.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.pal_copy`, `Complexity.pal_copy_end`, `Complexity.pal_rewind`, `Complexity.pal_test_start`, `Complexity.pal_test`.
