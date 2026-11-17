<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universalStateWindow_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Next Unary Cell

**Claim.** For all natural numbers $j$ and $n$, the state window with $j$ consumed symbols and $n+1$ remaining symbols contains $1$ at cell $j+1$.

**Proof.** At $z=j+1$, the cell is nonzero and satisfies $j<j+1\le j+(n+1)$, since $n+1\ge1$. Thus the defining interval condition for the state window holds, so its value there is $\mathrm{some}\;\mathrm{true}$.
