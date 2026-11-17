<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPL_subset_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPL is contained in deterministic polynomial time

**Claim.** Every Boolean language decidable in bounded-error probabilistic logarithmic space is decidable in deterministic polynomial time.

**Proof.** Take a bounded-error log-space machine $N$ deciding $L$, with space factor $c$. For an input $x$, choose $e=\mathrm{codeK}(N)(c+1)$ and let $V=8^e(|x|+1)^e$. The coding bound (`Randomized.BPLInP.two_pow_codes_le`) makes $V$ large enough for the configuration-counting arguments: the machine halts within $V$ choices (`Randomized.BPLInP.haltsWithin_of_codes`), and dynamic programming over configurations computes a value equal to $2^V$ times the probability of outputting true at time $V$ (`Randomized.BPLInP.dpVal_init`). Since the machine has halted, its output probabilities at $V$ agree with those at its original halting time (`Turing.FinNDTM.outputProb_eq_of_haltsWithin`).

The deterministic test `bplTest` compares the dynamic-programming count with half of $2^V$. Its correctness equivalence (`Randomized.BPLInP.bplTest_eq`) identifies this test with the strict majority threshold for the true-output probability. If $x\in L$, that probability is at least $2/3$, so the test accepts. If $x\notin L$, the false-output probability is at least $2/3$; the true and false output events are disjoint, and their total probability is at most one (`Randomized.randProb_or_disjoint`, `Randomized.randProb_le_one`), so the true-output probability is at most $1/3$ and the test rejects. Hence the test decides $L$. It is polynomial-time computable (`Randomized.BPLInP.polyTimeComputable_bplTest`), and every language decided by a polynomial-time computable Boolean test belongs to P (`Complexity.mem_P_of_test`).

**Key facts.** `Randomized.BPLInP.two_pow_codes_le`, `Randomized.BPLInP.haltsWithin_of_codes`, `Randomized.BPLInP.dpVal_init`, `Turing.FinNDTM.outputProb_eq_of_haltsWithin`, `Randomized.BPLInP.bplTest_eq`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_le_one`, `Randomized.BPLInP.polyTimeComputable_bplTest`, `Complexity.mem_P_of_test`.
