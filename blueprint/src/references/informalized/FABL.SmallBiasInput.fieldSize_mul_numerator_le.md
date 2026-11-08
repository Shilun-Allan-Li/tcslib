<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldSize_mul_numerator_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field Size Times Bias Numerator Bound

**Claim.** The field size times the bias numerator satisfies $2^D a\le 4nb$.

**Proof.** Because $n>0$, one has $b\le nb$. Also $a\le b$, since $a\le 2a\le b$. Consequently $a\le nb$. The field-size estimate $2^D\le 2S$ (\texttt{SmallBiasInput.fieldSize\_le\_two\_scale}) now gives $2^D a\le 2Sa$. The rounded-up quotient defining $S$ satisfies $Sa\le nb+a$ (\texttt{SmallBiasInput.scale\_mul\_numerator\_le}), so $2Sa\le 2(nb+a)$. Finally, using $a\le nb$, we obtain $2(nb+a)\le 4nb$. Chaining these inequalities proves the claim.

**Key facts.** `FABL.SmallBiasInput.fieldSize_le_two_scale`, `FABL.SmallBiasInput.scale_mul_numerator_le`.
