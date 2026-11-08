<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.isNegOnePivotal_booleanDual_negate_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality and pivotal outputs

**Claim.** The Boolean dual of $f$ is pivotal with output $-1$ at the coordinatewise negation of $x$ exactly when $f$ is pivotal with output $1$ at $x$.

**Proof.** At the negated point, the Boolean dual evaluates to $-f(x)$. Flipping coordinate $i$ there is the same as negating the point obtained by flipping coordinate $i$ in $x$; hence the dual’s value after that flip is $-f(x^{(i)})$, where $x^{(i)}$ denotes the coordinate-flipped point. Thus the two pivotality conditions are equivalent, since negation is injective. For the output condition, $-f(x)=-1$ is equivalent to $f(x)=1$. More explicitly, each value of $f$ is either $1$ or $-1$, so checking those two possibilities shows that the conjunction of the dual output condition and dual pivotality is equivalent to the conjunction of $f(x)=1$ and its pivotality at $i$.

**Key facts.** `FABL.flipCoordinate_negateSignCube`.
