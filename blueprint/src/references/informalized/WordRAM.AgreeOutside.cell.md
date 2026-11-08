<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.AgreeOutside.cell -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement at an outside cell

**Claim.** If two memories agree at every address outside $s$, then they have equal values at each particular address outside $s$.

**Proof.** Fix an address $a$ outside $s$. The assumed agreement is equality of the two memories at every point of the complement of $s$; since $a$ lies in that complement, it gives $m'(a)=m(a)$.
