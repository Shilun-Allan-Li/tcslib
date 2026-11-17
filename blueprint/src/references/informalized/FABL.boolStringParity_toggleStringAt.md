<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.boolStringParity_toggleStringAt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity under a coordinate toggle

**Claim.** Toggling coordinate $i$ of a Boolean string changes its parity in $\mathbb{F}_2$ by $1$.

**Proof.** Separate the parity sum into the term at $i$ and all terms at other coordinates. The toggle leaves every other coordinate unchanged, so their contribution is unchanged. At coordinate $i$, negating the Boolean changes its encoding from $a$ to $a+1$ in $\mathbb{F}_2$ (\(\texttt{FABL.pcppBoolF₂Equiv_not}\)). Reassembling the sum shows that the total parity is the original parity plus $1$.

**Key facts.** `FABL.pcppBoolF₂Equiv_not`.
