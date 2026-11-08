<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.pairValid_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-step pair validity scan

**Claim.** Suppose $x=pbc r$, where $p,r$ are Boolean words and $b,c$ are bits. Starting in the scan state at position $|p|$ with empty output, after two steps the tester remains scanning at position $|p|+2$ with empty output if $b=c$. If $b\ne c$, it halts at position $|p|+2$ and outputs the bit true exactly when $b=0$ and $c=1$.

**Proof.** Because the input begins with $pbc r$, the next scanned symbol from position $|p|$ is $b$. The tester's transition in the scan state moves right without output; by the one-step scanning fact `scanStep_right`, it advances to position $|p|+1$ and enters the state remembering $b$. Its next symbol is $c$. If $b=c$, the transition again moves right without output and returns to the scan state. If $b\ne c$, it halts and emits $\neg b\wedge c$, which is true precisely for $(b,c)=(0,1)$. Applying `scanStep_right` to this second transition and composing the two steps gives the stated configurations and output.

**Key facts.** `Turing.FinTM.scanStep_right`.
