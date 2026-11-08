<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/SocialChoiceFunctions/MayTheorem.lean :: FABL.may_theorem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Symmetric monotone odd functions

**Claim.** A symmetric, monotone, odd Boolean function on the sign cube can exist only when $n$ is odd, and then it is the majority function, with ties assigned value $1$.

**Proof.** First show that $n$ is odd. If $n$ were even, write $n=2k$ and choose the canonical input with $k$ positive coordinates. Its negation also has $k$ positive coordinates. Symmetry says that inputs with equal positive-coordinate counts have equal function values, so the function takes the same value at these two inputs. Oddness says their values are negatives of one another. Since the function only takes the values $-1$ and $1$, this is impossible. Thus $n$ is odd.

Now symmetry implies that the function's value at any input equals its value at the canonical input with the same number of positive coordinates. We show that any input $z$ with positive coordinate sum has function value $1$. The sum identity expresses that sum as twice the positive-coordinate count minus $n$, so positivity implies that the count of positive coordinates exceeds the count of negative ones. The canonical input with the latter count is coordinatewise below the canonical input with the former count. Monotonicity orders their function values. By symmetry, these values are respectively the values at $-z$ and $z$; oddness identifies the former as the negative of the latter. The only sign-valued possibility consistent with this order is $f(z)=1$.

Finally, for odd $n$, the coordinate sum is never zero. If it is positive, the preceding argument gives $f(x)=1$, matching the threshold definition of majority. If it is negative, the sum at $-x$ is positive, so $f(-x)=1$; oddness then gives $f(x)=-1$, again matching that threshold. Thus the function agrees with majority at every input.

**Key facts.** `FABL.positiveCoordinateCount_canonicalCountInput`, `FABL.positiveCoordinateCount_negateInput`, `FABL.isSymmetric_iff_eq_of_positiveCoordinateCount_eq`, `FABL.sum_signValue_eq_two_mul_positiveCoordinateCount_sub`, `FABL.canonicalCountInput_mono`, `FABL.positiveCoordinateCount_le`, `FABL.sum_signValue_ne_zero_of_odd`, `FABL.thresholdSign_of_nonneg`, `FABL.thresholdSign_of_neg`.
