<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.Steps.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Concatenation of Machine Runs

**Claim.** If $c$ reaches $c_1$ in $n$ steps and $c_1$ reaches $c_2$ in $k$ steps, then $c$ reaches $c_2$ in $n+k$ steps.

**Proof.** Proceed by induction on $n$, allowing the initial configuration to vary. If $n=0$, the first run says $c=c_1$, so the second run gives the required run from $c$ to $c_2$; its length is $0+k=k$. If $n$ is a successor, the first run supplies a configuration $c'$ such that one step takes $c$ to $c'$ and the remaining $n$ steps take $c'$ to $c_1$. Apply the induction hypothesis to those remaining steps and the given $k$-step run, obtaining a run from $c'$ to $c_2$ of length $n+k$. Prepending the first step gives the desired run. The resulting length is $1+(n+k)$, which equals $(n+1)+k$ by associativity and commutativity of addition on natural numbers.
