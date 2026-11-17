<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_prod_left_eq_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional mutual information chain rule

**Claim.** The conditional mutual information of the pair $(X,W)$ with $Y$ given $Z$ equals $I[X:Y\mid Z;\mu]+I[W:Y\mid (X,Z);\mu]$.

**Proof.** Write each conditional mutual information as a difference of conditional entropies. The proof first observes that the conditioning variables $(X,(Y,Z))$ and $(Y,(X,Z))$ are injective recodings of one another, so conditioning $W$ on either gives the same entropy; this is invariance of conditional entropy under injective recoding (\texttt{condEntropy\_of\_injective'}). Now apply the conditional entropy chain rule (\texttt{cond\_chain\_rule'}) to expand the entropies involving the pair $(X,W)$, once with conditioning by $Z$ and once by $(Y,Z)$. In both expansions, the reordered conditional entropy cancels by the recoding equality. The remaining terms are exactly the two conditional mutual informations on the right, proving the asserted chain rule.

**Caveat.** The proof source uses the conditional mutual information entropy-difference formula, the conditional entropy chain rule, and invariance under injective recoding; these are not included in the supplied upstream list.
