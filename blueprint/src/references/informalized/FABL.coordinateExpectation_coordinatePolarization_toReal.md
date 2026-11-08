<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.coordinateExpectation_coordinatePolarization_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polarization Preserves Coordinate Expectation

**Claim.** The coordinate expectation of the real-valued polarization of a Boolean function equals the coordinate expectation of the original function.

**Proof.** Fix an input $x$, and write $a=f(x_{i	o 1})$ and $b=f(x_{i	o -1})$. By the coordinate expectation formula, the polarized function's expectation at $x$ is the average of its values at these two updated inputs. The polarization identities say those values are respectively $4	ext{max}(a,b)$ and $4	ext{min}(a,b)$, interpreted as real numbers. Since $a$ and $b$ are signs, their maximum and minimum are just the same two values in some order; hence their sum is $a+b$. Thus the average is $(a+b)/2$, the original function's coordinate expectation. This holds at every $x$.

**Key facts.** `FABL.coordinateExpectation_apply`, `FABL.coordinatePolarization_setCoordinate_one`, `FABL.coordinatePolarization_setCoordinate_neg_one`.
