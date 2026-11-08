<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.hasSignRange_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign range of the real-valued function

**Claim.** For every input, the real-valued function obtained from a Boolean function takes one of the values $-1$ and $1$.

**Proof.** Fix an input $x$. Every unit in the integers is either $1$ or $-1$ (`Int.units_eq_one_or`). Applying this to the output at $x$, and then viewing that integer as a real number, shows that the value is $1$ or $-1$.
