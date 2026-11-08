<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasAlgorithm.lean :: FABL.SmallBiasInput.fieldSize_le_four_dimension_div_epsilon -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Field Size in Terms of Dimension and Bias

**Claim.** For $\varepsilon=a/b$, the field size satisfies $2^D\le 4n/\varepsilon$.

**Proof.** First, $a>0$ by hypothesis, and $b>0$ because $2a\le b$ with $a>0$. The established integer estimate $2^D a\le 4nb$ (\texttt{SmallBiasInput.fieldSize\_mul\_numerator\_le}) therefore transfers to the reals as $(2^D)a\le 4nb$. By the definition $\varepsilon=a/b$, the right-hand side of the desired inequality is $4nb/a$. Dividing the transferred inequality by the positive number $a$ yields $2^D\le 4nb/a=4n/\varepsilon$.

**Key facts.** `FABL.SmallBiasInput.fieldSize_mul_numerator_le`.
