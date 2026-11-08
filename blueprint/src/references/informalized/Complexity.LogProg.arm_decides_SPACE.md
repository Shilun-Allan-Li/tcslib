<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ARMWidth.lean :: Complexity.LogProg.arm_decides_SPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Logarithmic-space simulation

**Claim.** Under the stated halting, correctness, side-condition, and register-size hypotheses, the language decided by the oracle register program belongs to $\mathrm{SPACE}(S)$.

**Proof.** For each oracle language $A_j$, its membership in logarithmic space supplies a decider using at most $c_j\logSpace(v)$ space on inputs of length $v$. Since there are finitely many oracles, choose one such constant $c_j$ for each and let $c_* = \sum_j c_j$; in particular, $c_j\le c_*$. The general register-program simulation theorem (`arm_decides_space`) applies with register-word bound $W(n)=K S(n)$, provided oracle inputs of the lengths produced by calls can be handled within a constant multiple of $S(n)$.

Fix an input of length $n$ and put $P=2^{S(n)}$. The hypothesis $\logSpace(n)\le S(n)$, together with the fact that $n+1\le 2^{\logSpace(n)}$ (`succ_le_two_pow_log`), gives $n+1\le P$. Also $S(n)\le P$ and $S(n)\ge1$. The call-input length estimate in the simulation proof then bounds any relevant oracle input length $v$ by $A_0P$, where $A_0=2+2m+2mK$: the input itself, the at most $m$ register words, and their separators are all covered by this bound. The logarithmic growth estimate `logSpace_le_of_le_mul_two_pow` consequently gives $\logSpace(v)\le(A_0+1)S(n)$.

Thus every oracle decider uses at most $c_j(A_0+1)S(n)\le c_*(A_0+1)S(n)$ space on a call. The register simulation also accounts for the program's own registers, at most $K S(n)$, by taking the overall constant to be $K+c_*(A_0+1)$. Since $S(n)\ge1$, this constant absorbs the bounds required by `arm_decides_space`; the assumed correct halting run therefore yields $L\in\mathrm{SPACE}(S)$.

**Key facts.** `Complexity.LogProg.arm_decides_space`, `Complexity.LogProg.succ_le_two_pow_log`, `Complexity.logSpace_le_of_le_mul_two_pow`.
