<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPTIMEThreshold.lean :: Randomized.BPTIMEWith_eq_BPTIME -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equivalence of BPP Threshold Definitions

**Claim.** For any acceptance threshold strictly between $1/2$ and $1$, the class defined using that threshold is the same as the class defined using threshold $2/3$.

**Proof.** First use the theorem identifying the $2/3$-threshold class with BPTIME (`Randomized.BPTIMEWith_two_thirds`), and prove the two inclusions between the threshold-$\rho$ class and the $2/3$-threshold class.

1. Put $\varepsilon=\rho-1/2$, which is positive. Since $1/2<\rho<1$, the quantity $1-4\varepsilon^2$ is strictly less than $1$. Choose a repetition count $n$ large enough that the amplification estimate's error parameter satisfies $2(1-4\varepsilon^2)^n\le 1/3$. The amplification theorem converts threshold $1/2+\varepsilon=\rho$ into threshold $1-1/3=2/3$ (`Randomized.BPTIMEWith_subset_of_amp`). This proves the inclusion from threshold $\rho$ to threshold $2/3$.
2. For the reverse inclusion, set $\varepsilon=1/6$. Then $1/2+\varepsilon=2/3$, and again $1-4\varepsilon^2<1$. Choose $n$ large enough that $2(1-4\varepsilon^2)^n\le (1-\rho)/2$. Amplification now yields threshold $1-(1-\rho)/2$, which is at least $\rho$. Lowering the threshold to $\rho$ preserves membership by probability monotonicity (`Randomized.BPTIMEWith_anti`). This gives the reverse inclusion and hence equality.

**Key facts.** `Randomized.BPTIMEWith_two_thirds`, `Randomized.BPTIMEWith_subset_of_amp`, `Randomized.BPTIMEWith_anti`.
