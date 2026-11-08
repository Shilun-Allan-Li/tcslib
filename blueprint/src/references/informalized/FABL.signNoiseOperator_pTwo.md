<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ProductHypercontractivity.lean :: FABL.signNoiseOperator_pTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-Point Noise Hypercontractivity

**Claim.** If $1\le p\le2$ and $0\le\rho\le\sqrt{p-1}$, then the $L^2$ norm of the sign noise operator applied to $f$ is at most the $L^p$ norm of $f$, under the uniform probability measure on the sign set.

**Proof.** First convert both norms defined through the uniform probability mass function into the corresponding uniform $L^p$ norms (`pmfLpNorm_uniform_eq_uniformLpNorm`). The function produced by the noise operator has the form $a+\rho b\,\operatorname{signValue}(x)$, where $a$ and $b$ are the even and odd coefficients of $f$. The two-point hypercontractive inequality bounds its uniform $L^2$ norm by the uniform $L^p$ norm of $a+b\,\operatorname{signValue}(x)$ (`oneBit_pTwo`), using the stated bounds on $p$ and $\rho$. Finally, affine reconstruction identifies this latter function with $f$ at every sign (`sign_affine_reconstruct`), giving the desired inequality.

**Key facts.** `FABL.pmfLpNorm_uniform_eq_uniformLpNorm`, `FABL.oneBit_pTwo`, `FABL.sign_affine_reconstruct`.
