<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.readField_fcode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a Coded Field

**Claim.** For any bit strings $w,r$ and bit $e$, reading the field code of $w$ followed by $e$, the delimiter $0$, and $r$ returns exactly $(w,r)$.

**Proof.** Induct on $w$. If $w$ is empty, its field code is empty, so the reader encounters $e,0$ immediately: it recognizes the delimiter and returns the empty word together with $r$. If $w=b::w'$, its field code begins with $b,1$, which the reader consumes as the code for the first bit and then recursively reads the field code of $w'$ followed by the same delimiter and remainder. By the induction hypothesis that recursive read returns $(w',r)$; prepending $b$ to the decoded word gives $(w,r)$.
