<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.expect_e3LinPredicate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability of a Three-Variable Linear Predicate

**Claim.** For either right-hand side in $\mathbb F_2$, a uniformly random triple satisfies the maximum three-variable linear predicate with probability $1/2$.

**Proof.** Represent the right-hand side by a Boolean bit and identify each element of $\mathbb F_2$ with its corresponding Boolean value. These bijections preserve uniform averages, so it suffices to average over three independent Boolean inputs. The proof then factors this average into three successive averages, one for each input. Each Boolean value corresponds to $0$ or $1$ in the field, each occurring once. Evaluating the predicate on these possibilities for each right-hand-side bit gives exactly half of the eight triples as satisfying, and hence the average acceptance indicator is $1/2$.

**Key facts.** `FABL.boolF₂Equiv_false`, `FABL.boolF₂Equiv_true`.
