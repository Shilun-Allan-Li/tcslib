<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.F₂LinearEquation.isSatisfied_add_iff_of_isSatisfied_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfaction after adding an equation

**Claim.** If an assignment satisfies the right equation, then it satisfies the sum of the left and right equations exactly when it satisfies the left equation.

**Proof.** Evaluation respects addition of equations (\texttt{eval\_add}). Since the assignment satisfies the right equation, the condition that it satisfies the sum becomes $L_1(x)+c_2=c_1+c_2$, where $c_i$ is the constant of $L_i$. In $\mathbb F_2$, adding $c_2$ to both sides cancels it because $c_2+c_2=0$. Thus this condition is equivalent to $L_1(x)=c_1$, precisely satisfaction of the left equation.

**Key facts.** `FABL.F₂LinearEquation.eval_add`.
