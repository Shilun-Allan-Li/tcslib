<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.not_mem_majorityHeadCoalition_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Right Summand Avoids the Head Coalition

**Claim.** For natural numbers $k,m$ and any $j<m$, the index associated to $j$ in the right summand does not belong to the coalition of the first $k$ indices.

**Proof.** Suppose the right-summand index belonged to the coalition. Membership in the mapped finite set would give some left-summand index with the same image under the disjoint-sum equivalence. Injectivity of that equivalence would then identify a left-summand element with a right-summand element, which is impossible because the two summands are disjoint. Thus the index is outside the coalition.
