<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.odd_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Oddness of the real-valued function

**Claim.** If a Boolean function $f$ is odd, then its real-valued version $f.toReal$ is odd: for every input $x$, $(f.toReal)(-x)=-(f.toReal)(x)$.

**Proof.** Fix an input $x$. By definition, the real-valued version applies the sign-value map to the output of $f$. Oddness of $f$ gives $f(-x)=-f(x)$, so the left side becomes the sign value of $-f(x)$. The sign-value map sends negation to real negation (\texttt{signValue\_neg}), yielding the sign-value of $f(x)$ with a minus sign, which is exactly $-(f.toReal)(x)$.

**Key facts.** `FABL.signValue_neg`.

**Caveat.** The supplied informal statement describes definitions rather than this theorem; the claim and proof follow the formal statement and proof source.
