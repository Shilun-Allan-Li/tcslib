<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LinearThresholdBias.lean :: FABL.odd_of_balanced_affineLinearThresholdRepresentation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced Threshold Functions Are Odd

**Claim.** If a Boolean function on the sign cube has an affine linear threshold representation and is balanced, then it is odd: negating the input negates the function value.

**Proof.** First average the paired values $f(x)+f(-x)$ over the cube. The expectation of the second summand equals that of the first by invariance of the uniform cube under negation (\texttt{expect\_neg\_input}); balance makes their sum zero. We next show that each paired sum is either always nonnegative or always nonpositive. If $a_0\ge 0$, the affine forms at $x$ and $-x$ are $a_0+t$ and $a_0-t$, where $t$ is the linear form at $x$ (\texttt{affineLinearForm\_neg\_input}). Their threshold signs have nonnegative sum (\texttt{thresholdPair\_nonneg\_of\_bias\_nonneg}), so $f(x)+f(-x)\ge0$ for every $x$. A function that is everywhere nonnegative on a finite uniform space and has expectation zero must vanish at every point; hence every paired sum is zero. If instead $a_0<0$, the corresponding threshold-sign sum is nonpositive (\texttt{thresholdPair\_nonpos\_of\_bias\_neg}); the same zero-expectation argument again makes every paired sum zero. Thus in all cases $f.toReal(-x)=-f.toReal(x)$. Since the real-valued encoding of signs is injective (\texttt{signValue\_injective}) and sends a negated sign to the negative real value (\texttt{signValue\_neg}), this equality implies $f(-x)=-f(x)$, as claimed.

**Key facts.** `FABL.expect_neg_input`, `FABL.affineLinearForm_neg_input`, `FABL.thresholdPair_nonneg_of_bias_nonneg`, `FABL.thresholdPair_nonpos_of_bias_neg`, `FABL.signValue_injective`, `FABL.signValue_neg`.
