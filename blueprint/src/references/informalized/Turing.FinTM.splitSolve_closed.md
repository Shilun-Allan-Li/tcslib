<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSolve_closed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Solver Existence

**Claim.** For every $C,e\in\mathbb N$, some finite Boolean Turing machine computes the specified encoded least split, or the empty word if there is no valid split, in at most $c(|w|+1)^{e+2}$ steps for some natural number $c$.

**Proof.** Split on $e$. When $e=0$, use the machine that prepends a fixed block of $C$ ones as the source. `splitSource_constant` verifies that on a candidate of length $\ell$ this produces the required $C$ tally bits in $C+1$ steps, and the elementary bound on that time supplies the source hypothesis for `splitSolve_source`. When $e$ is positive, write it as $r+1$ and use the polynomial unary catalog machine with parameter $r$. `splitSource_poly` verifies that this machine produces $C(\ell+1)^{r+1}$ tally bits in `catalogPolyCost` steps. The estimate `catalogPolyCost_le` bounds this cost by $(C+1+5(r+1)) (\ell+1)^{r+1}$; adding one yields the required source-time bound. In either case, `splitSolve_source` converts the source contract and its time bound into a finite machine computing the required split function in a polynomial bound of degree $e+2$.

**Key facts.** `Turing.FinTM.splitSource_constant`, `Turing.FinTM.splitSolve_source`, `Turing.FinTM.splitSource_poly`, `Turing.FinTM.catalogPolyCost_le`.
