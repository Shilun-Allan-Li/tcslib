<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.linearForm_and_centeredSquare_fourthMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourth Moment Bounds for Linear Forms

**Claim.** For every dimension and coefficient vector, the fourth moment of a linear form on the Boolean cube is at most nine times the square of its second moment. The centered square of that linear form likewise has fourth moment at most eighty-one times the square of its second moment.

**Proof.** Proceed by induction on the dimension. In dimension zero, both functions are identically zero, so both inequalities hold. For the induction step, split a vector into its first sign $b$ and its remaining coordinates $x$. Write the linear form on the remaining coordinates as $e(x)$ and let $d(x)=a_0$. The prefixed linear form is $b d(x)+e(x)$, by the decomposition of a linear form on a prefixed sign vector (`linearForm_fin_cons`). The fourth-moment estimate for a sign slice (`fourthMoment_le_nine_of_slice`), together with the induction hypothesis for $e$ and the immediate fourth-moment bound for the constant $d$, gives the factor-nine inequality.

For the centered square, take $e(x)$ to be the centered square formed from the remaining coefficients and take $d(x)$ to be the linear form with coefficients $2a_0a_i$. Expanding the square of $a_0b+L(x)$ and using $b^2=1$ shows that the centered square on the prefixed vector equals $b d(x)+e(x)$. Here $b^2=1$ follows because every sign is either $-1$ or $1` (`signValue_eq_neg_one_or_one`). The induction hypotheses give the factor-nine fourth-moment bound for $d$ and the factor-eighty-one bound for $e$. The sign-slice estimate for this pair (`fourthMoment_le_eightyOne_of_slice`) then yields the factor-eighty-one bound in dimension $n+1$.

**Key facts.** `FABL.linearForm_fin_cons`, `FABL.fourthMoment_le_nine_of_slice`, `FABL.signValue_eq_neg_one_or_one`, `FABL.fourthMoment_le_eightyOne_of_slice`.
