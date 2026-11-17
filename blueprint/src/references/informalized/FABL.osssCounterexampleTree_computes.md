<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeExercises.lean :: FABL.osssCounterexampleTree_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the counterexample tree

**Claim.** For every real $t$, the specified decision tree computes the function $f_t$ on every input in the three-dimensional sign cube.

**Proof.** Two functions on the sign cube are equal if they agree at each input, so fix an input $x$. Each coordinate is either $1$ or $-1$. Split into these two possibilities for each of $x_0,x_1,x_2$, giving the eight sign assignments. In each case the tree follows the branch specified by those signs and returns its prescribed leaf value; substituting the same signs into the displayed formula for $f_t$ simplifies to that value. The equality is a direct real-algebra calculation in each case, valid for arbitrary $t$.
