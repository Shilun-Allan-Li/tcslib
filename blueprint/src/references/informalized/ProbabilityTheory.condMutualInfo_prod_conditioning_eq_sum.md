<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_prod_conditioning_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Conditional mutual information decomposition

**Claim.** Conditioning on the pair $(K,Z)$ decomposes the conditional mutual information into the sum, over $k$, of the mass of the event $K=k$ times the conditional mutual information given $Z$ under the measure conditioned on $K=k$.

**Proof.** Expand the left-hand conditional mutual information as a sum over the values $(k,z)$ of the conditioning variable, using its fiber-sum formula (\texttt{condMutualInfo\_eq\_sum'}). Expand each conditional mutual information on the right as a sum over $z$ by the same formula, and distribute the factor $\mu(K=k)$ across that sum. Reindexing the left sum over pairs $(k,z)$ aligns the two sums. For fixed $k,z$, let $A=\{K=k\}$ and $F=\{Z=z\}$. The joint fiber is $A\cap F$. Conditioning first on $A$ and then on $F$ is conditioning directly on $A\cap F$ (\texttt{cond\_cond\_eq\_cond\_inter}); because $F\subseteq A$ is not generally true, the relevant event for the second conditioning is precisely the intersection, and the support identity identifies the conditional mass there. The mass identity $\mu(A)(\mu[\cdot\mid A])(F)=\mu(A\cap F)$ follows from the measure-times-conditioned-measure formula for subsets (\texttt{measureReal\_mul\_cond\_real\_eq\_measureReal\_of\_subset}). Thus each summand on the two sides agrees, after rearranging its factors, and summing proves the identity.

**Key facts.** `ProbabilityTheory.measureReal_mul_cond_real_eq_measureReal_of_subset`.

**Caveat.** The supplied upstream list omits the fiber-sum expansion and the iterated-conditioning identity used in the proof source. Also, the source obtains its iterated-conditioning step via the intersection identity; the paraphrase above follows that route, but the given informal statement alone does not record the fiber-level calculations.
