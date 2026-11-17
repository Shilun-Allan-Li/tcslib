<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CounterProgRun.lean :: Complexity.CounterProg.goes_loop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count-Down Loop

**Claim.** Under the stated zero-test, decrement, and body assumptions, the loop reaches the exit with register assignment $\sigma_K$ and input position $p_K$, appending the concatenation of $e_0,\ldots,e_{K-1}$, within $K(b+2)+1$ steps.

**Proof.** We prove a reverse-counted induction statement. For each $i\le K$, starting at the head with assignment $\sigma_{K-i}$ and position $p_{K-i}$ reaches the exit with assignment $\sigma_K$ and position $p_K$ within $i(b+2)+1$ steps. The output appended is the concatenation of the strings $e_j$ for indices $j=K-i,\ldots,K-1$.

For $i=0$, the starting assignment is $\sigma_K$. The hypothesis gives $\sigma_K(r)=K-K=0$, so the zero-test rule (`Complexity.CounterProg.goes_jz_zero`) takes the loop directly to the exit, preserving registers, position, and output, in one step.

For the successor case, let $i+1\le K$. At the head, the current register value is $K-(K-(i+1))=i+1$, hence is positive. The positive-test rule (`Complexity.CounterProg.goes_jz_pos`) takes the program to the decrement label in one step. The decrement rule (`Complexity.CounterProg.goes_dec`) then takes it to the body in one further step and changes register $r$ to $i$. This is exactly the updated assignment required by the body hypothesis for iteration $K-(i+1)$: its specified replacement value $K-(K-(i+1))-1$ equals $i$. The body hypothesis reaches the head with assignment $\sigma_{K-i}$, position $p_{K-i}$, and appends $e_{K-(i+1)}$, using at most $b$ steps. Applying the induction hypothesis for $i$ completes the run. Concatenating these runs appends the current iteration's output before the outputs of the remaining iterations, and their step bounds sum to $1+1+b+i(b+2)=(i+1)(b+2)+1$. Taking $i=K$ proves the claim; the indexed concatenation is then exactly the concatenation over $e_0,\ldots,e_{K-1}$.

**Key facts.** `Complexity.CounterProg.goes_jz_zero`, `Complexity.CounterProg.goes_jz_pos`, `Complexity.CounterProg.goes_dec`, `Complexity.CounterProg.Goes.trans`, `Complexity.CounterProg.Goes.congr`.
