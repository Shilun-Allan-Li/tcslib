<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.two_mul_blrIndicator_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR Indicator Sign Identity

**Claim.** For $a,b,c\in\mathbb F_2$, twice the indicator of $a+b=c$, minus one, equals the product of the three associated signs.

**Proof.** Replace each encoded sign by the corresponding binary character, using `FABL.signValue_signEncode_eq_binarySign`. Because the binary character sends addition to multiplication, the product of the three signs is the character evaluated at $a+b+c$. If $a+b=c$, then $a+b+c=0$ in $\mathbb F_2$: indeed, $-c=c$ there, so $c+c=0$. The character at zero is $1$, matching $2\cdot1-1$. If $a+b\ne c$, then $a+b+c\ne0$; the only nonzero element of $\mathbb F_2$ is $1$. The character at $1$ is $-1$, matching $2\cdot0-1$.

**Key facts.** `FABL.signValue_signEncode_eq_binarySign`.
