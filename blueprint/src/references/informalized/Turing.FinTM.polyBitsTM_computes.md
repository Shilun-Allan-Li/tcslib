<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.polyBitsTM_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Bit Generation

**Claim.** For every $C,e\in\mathbb N$, a finite Boolean Turing machine computes the binary digit list of $C(|x|+1)^e$ on each Boolean input $x$, within $(7C+5e+11)(|x|+1)^e$ steps.

**Proof.** Fix an input $x$ and put $P=(|x|+1)^e$, so $1\le P$. First suppose $C=0$. The machine is the constant-output machine for the binary digits of zero, which halts in the length of that output plus one steps. Since that output is empty, this is one step, and it is within the claimed bound.

If $C\ne0$ and $e=0$, the machine outputs the constant word of binary digits of $C$. The constant-machine computation takes $|\mathrm{bits}(C)|+1$ steps, and the bound $|\mathrm{bits}(C)|\le C$ shows this is at most $C+1$, hence within the stated bound at $e=0$.

Finally, let $e=d+1$. The polynomial unary machine first produces $C P$ copies of $1$, in $(C+5e+4)P$ steps. The length-bit machine applied to that unary word outputs the binary digits of its length, namely $C P$, in $5(CP+1)$ steps. Buffered composition adds the unary output length and two setup steps, so the combined computation takes $(C+5e+4)P+CP+2+5(CP+1)$ steps. This equals $(7C+5e+4)P+7$. Since $P\ge1$, we have $7\le7P$, giving the target bound $(7C+5e+11)P$. The time monotonicity principle (`ComputesInTime.mono`) then allows the exact computation to be stated at that larger bound.

**Key facts.** `Turing.FinTM.constTM_computes`, `Turing.length_bits_le_self`, `Turing.FinTM.polyUnaryTM_computes`, `Turing.FinTM.lengthBitsTM_computes`, `Turing.FinTM.bufferedCompTM_computesInTime`, `Turing.FinTM.ComputesInTime.mono`.
