<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.tendsto_one_sub_exp_neg_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential difference quotient limit

**Claim.** As \(x\to0\) through nonzero real values, \((1-e^{-x})/x\) tends to one.

**Proof.** The function \(x\mapsto e^{-x}\) has derivative \(-1\) at zero, by the chain rule and the derivative of the exponential. Therefore \(x\mapsto1-e^{-x}\) has derivative \(1\) at zero. The derivative is the limit of the corresponding difference quotient at zero; since the numerator vanishes there, that quotient is exactly \((1-e^{-x})/x\) for nonzero \(x\).
