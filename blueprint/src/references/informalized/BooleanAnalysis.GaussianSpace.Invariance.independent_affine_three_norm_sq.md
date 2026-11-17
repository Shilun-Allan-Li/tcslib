<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/GaussianSpace/Invariance/ThirdMoments.lean :: BooleanAnalysis.GaussianSpace.Invariance.independent_affine_three_norm_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Affine norm bound under independence

**Claim.** If $A,D$ lie in $L^3$, $X$ satisfies the stated hypercontractivity and moment assumptions, and $X$ is independent of $(A,D)$, then $N_3(A+DX)^2\le N_3(A)^2+N_3(D/\rho)^2$.

**Proof.** First pass from $\mu$ to the law of $X$. The affine hypercontractive estimate (\texttt{IsHypercontractive.affine\_three\_norm\_sq}) shows that for every $a,b$, the squared $L^3$ norm of $a+bX$ is at most $a^2+(b/\rho)^2$. Expressing this norm bound using the law of $X$ supplies the scalar hypothesis needed by the product estimate. Independence of $X$ and the pair $(A,D)$ identifies the joint law of $((A,D),X)$ with the product of the law of $(A,D)$ and the law of $X$. Apply the affine product estimate (\texttt{affine\_product\_three\_norm\_sq}) to those laws. Its conclusion bounds the squared norm of the function $(a,d,x)\mapsto a+dx$ by the sum of the squared norms of the first coordinate and $d/\rho$. Finally, transfer these norms back to $\mu$ using the corresponding pushforward-measure identities. Since $A,D,X\in L^3$ and $\rho>0$, the quantities are finite; converting the extended-real norm inequality to real norms yields the claimed bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.IsHypercontractive.affine_three_norm_sq`, `BooleanAnalysis.GaussianSpace.Invariance.affine_product_three_norm_sq`.
