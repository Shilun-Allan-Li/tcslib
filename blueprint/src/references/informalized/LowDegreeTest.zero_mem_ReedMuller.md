<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.zero_mem_ReedMuller -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero function lies in the Reed–Muller code

**Claim.** For every $d\in\mathbb N$, the identically-false function on the $n$-dimensional Boolean cube has degree at most $d$, and hence lies in $\mathrm{RM}(d,n)$.

**Proof.** We prove the defining condition by induction on $d$, with the starting point $x$ generalized so that the induction hypothesis applies at any input. When $d=0$, the relevant Gowers product has order one and reduces to the value of the lifted zero function at $x$. That value is $1$, since false is sent to the real sign $1$; this gives the required condition. For the step from $d$ to $d+1$, the Gowers product of order $d+2$ is the product of two Gowers products of order $d+1$: one based at $x$, the other based at the XOR translate of $x$ by the final direction. The induction hypothesis makes each factor equal to $1$, including at that translated input. Their product is therefore $1$, establishing the defining condition at the next degree.
