<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Uniform.lean :: BoolCircuit.encodeNat_prefixFree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix-Freeness of Natural Number Codes

**Claim.** For natural numbers $a,b$ and Boolean lists $s,t$, if the code for $a$ followed by $s$ equals the code for $b$ followed by $t$, then $a=b$ and $s=t$.

**Proof.** Induct on $a$. When $a=0$, its code is the terminator $[0]$. If $b=0$, equality after appending suffixes gives $s=t$; if $b$ is positive, its code begins with $1$, so equality with the code beginning in $0$ is impossible. For the successor case, if $b=0$, the same initial-bit comparison rules out equality. If $b$ is also a successor, both codes begin with $1$. Remove this common bit; the remaining equality is precisely an equality of the codes for the two predecessors followed by the same suffixes. The induction hypothesis identifies the predecessors and the suffixes, and therefore identifies $a$ with $b$ as well.
