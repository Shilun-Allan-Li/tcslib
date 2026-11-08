<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.exists_common_majorityAgreementCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Shared Majority Agreement Coordinate

**Claim.** For odd positive $d\le n$ and any two sign strings $x,y\in\{\pm1\}^n$, some coordinate among their first $d$ coordinates agrees with the majority of each string restricted to those coordinates.

**Proof.** Restrict $x$ and $y$ to their first $d$ coordinates, obtaining strings $x'$ and $y'$ on a $d$-element index set. For each string, consider the set of coordinates agreeing with its majority. The oddness of $d$ ensures a strict majority, and the majority-agreement counting result says that each of these two sets has cardinality strictly greater than $d/2$ (that is, $d<2$ times its cardinality) (`FABL.majorityAgreementCoordinates_card`). Their cardinalities therefore sum to more than $d$. Two subsets of a $d$-element set whose sizes sum to more than $d$ must intersect. A coordinate in the intersection agrees with both majorities; translating back through the restriction gives the desired coordinate of the original strings.

**Key facts.** `FABL.majorityAgreementCoordinates_card`.
