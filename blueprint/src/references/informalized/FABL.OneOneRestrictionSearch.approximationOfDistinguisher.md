<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.OneOneRestrictionSearch.approximationOfDistinguisher -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact-One Approximation

**Claim.** A one-one restriction search combined with a decision map distinguishing the exact-one promise yields a threshold approximation: on every valid instance the reconstructed solution is feasible, and if the optimum is at least $1$, its value is at least $1$.

**Proof.** Fix a valid input. The reconstruction is feasible by the search's feasibility guarantee. For the value bound, suppose the optimum is at least $1$. The search also guarantees that the optimum is at most $1$, so the optimum equals $1. The decision map correctly distinguishes the exact-one promise, and the search's exact-one preservation guarantee therefore says that the reconstructed solution has value exactly $1$. In particular, its value is at least the threshold $1$, as required.
