<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.exists_homogeneousLinearThresholdRepresentation_of_isBalanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneous representation of a balanced threshold function

**Claim.** A balanced linear threshold Boolean function has a homogeneous representation: some coordinate weights make the function equal at every input to the sign of the corresponding linear form, with zero assigned sign $+1$.

**Proof.** Write the given affine threshold representation using offset $a_0$ and weights $a$. Balancedness implies the function is odd under negating the input. Fix an input. If its value is $+1$, oddness makes the value at the negated input $-1$. The threshold representation then forces the affine form at the original input to be nonnegative and the form at the negated input to be strictly negative. Since negation changes the linear part from $L$ to $-L$, these inequalities imply $L>0$. If instead the value is $-1$, oddness gives value $+1$ at the negated input; the representation forces the original affine form to be strictly negative and the negated one nonnegative, which implies $L<0$. Thus the original value agrees with the threshold sign of $L$ in either case. Taking the same weights $a$ and offset zero proves the claim.

**Key facts.** `FABL.odd_of_balanced_affineLinearThresholdRepresentation`, `FABL.thresholdSign_of_neg`, `FABL.thresholdSign_of_nonneg`, `FABL.affineLinearForm_neg_input`.
