<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.wrote_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extending a written interval

**Claim.** Updating the function written on $dst\le x<dst+j$ at index $dst+j$ to value $f(j)$ gives the function written on the extended interval $dst\le x<dst+j+1$.

**Proof.** Compare the functions at an arbitrary index $a$. If $a=dst+j$, the update assigns $f(j)$, and the extended interval includes this endpoint with offset $j$, so the extended write also gives $f(j)$. Otherwise the update leaves the value at $a$ unchanged. If $a$ was in the original interval, it is also in the extended interval, and both writes use the same offset $a-dst$. If it was not in the original interval, then, since it is not the new endpoint, it is also outside the extended interval; both functions consequently retain $\mu(a)$.

**Key facts.** `Light.wrote_done`.
