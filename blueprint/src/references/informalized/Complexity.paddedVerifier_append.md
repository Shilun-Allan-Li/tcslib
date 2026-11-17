<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/NP.lean :: Complexity.paddedVerifier_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-Boundary Padded Verifier Characterization

**Claim.** If $|v|=(C+1)(|x|+1)^c$, then $xv$ belongs to the padded verifier for $C,c,V$ exactly when some $u$ is obtained by stripping the certificate from $v$, has length at most $C(|x|+1)^c$, and satisfies $\operatorname{pairEncode}(x,u)\in V$.

**Proof.** The length of $xv$ is $|x|+(C+1)(|x|+1)^c$. Thus $n=|x|$ satisfies the split equation $n+(C+1)(n+1)^c=|xv|$. The split specification (`certificateSplit_spec`) therefore says that the verifier's split is exactly $|x|$. Substituting this split into the definition of the padded verifier, the prefix of length $|x|$ is $x$ and the remaining suffix is $v$. The verifier's two remaining requirements are precisely that stripping this suffix yields some $u$ within the stated length bound and that $\operatorname{pairEncode}(x,u)$ belongs to $V$. This gives both directions of the characterization.

**Key facts.** `Complexity.certificateSplit_spec`.
