<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.mem_graphMatchingPartEdges_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching edge part membership

**Claim.** An edge of the perfect matching belongs to the subfamily associated with part $p$ exactly when it contains a vertex $(p,r)$ for some $r\in\{0,\ldots,k-1\}$.

**Proof.** The subfamily is defined by filtering the matching's edge set for edges containing a vertex of the form $(p,r)$ with $r$ in the $k$-element part. Thus an edge belongs to that subfamily precisely when such a position $r$ exists.
