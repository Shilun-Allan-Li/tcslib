<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean :: Turing.FinTM.sweepTime_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closed form for simulation time

**Claim.** For all natural numbers $k,t$, the recursively defined time function satisfies $\sigma_k(t)=2kt^2+(5k+4)t+(2k+2)$.

**Proof.** Proceed by induction on $t$. At $t=0$, the recursive definition gives $2k+2$, which is the displayed formula at zero. For the successor step, substitute the induction hypothesis into the recurrence: the added cost is $(4t+7)k+4$. Expanding the proposed formula at $t+1$ shows that its increase from the value at $t$ is exactly this amount, so the expressions agree.
