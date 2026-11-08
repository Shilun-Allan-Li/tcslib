<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.toggleStringAt_isOddWeight_of_not -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Toggling Changes Parity

**Claim.** If a Boolean string has even Hamming weight, toggling any one of its coordinates gives a string of odd Hamming weight.

**Proof.** Toggling a coordinate adds $1$ to the string's parity in $\mathbb F_2$ (`FABL.boolStringParity_toggleStringAt`). The original parity is either $0$ or $1$, since these are the only elements of $\mathbb F_2$ (`FABL.f₂_eq_zero_or_one`). It cannot be $1$, by the assumption that the original string is not odd, so it is $0$. Adding $1$ therefore gives parity $1$, as required.

**Key facts.** `FABL.boolStringParity_toggleStringAt`, `FABL.f₂_eq_zero_or_one`.
