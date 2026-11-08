<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading an unchanged cell

**Claim.** If two memories agree outside $s$, and $a$ is outside $s$ with $m(a)=v$, then $m'(a)=v$.

**Proof.** Because $a$ is outside $s$, the assumed agreement gives $m'(a)=m(a)$. Combining this equality with $m(a)=v$ yields $m'(a)=v$.
