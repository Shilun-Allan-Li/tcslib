<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Emod.lean :: Light.Emod.sign_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Execution of the Signed Remainder Step

**Claim.** Under the stated machine bounds and $a=|x|$, the signed remainder program starting with rest $a\bmod M$ and count zero reaches a state whose first local is $x\bmod M$, with memory unchanged, at cost at most $12$.

**Proof.** Let $r=a\bmod M$, so $r<M$ because $M\ge1$. The outer conditional separates the sign of $x$. If $x<0$, the identity for the remainder of a negative natural cast (`neg_emod_nat`) says that $(-a)\bmod M$ is zero when $r=0$ and otherwise is $M-r$. The inner conditional tests exactly these two cases, and assigns respectively $0$ or $M-r$ to the first local. Since $a=|x|$, this is $x\bmod M$. If $x\ge0$, the program assigns $r$ directly; the natural-to-integer remainder identity identifies this with $x\bmod M$. Each selected branch is a single assignment, and assignments preserve memory. The bounded conditional-execution principle (`Ends.iteLast`) and assignment principle (`Ends.setTo`) give the execution and its stated cost.

**Key facts.** `Light.neg_emod_nat`, `Light.Ends.iteLast`, `Light.Ends.setTo`.
