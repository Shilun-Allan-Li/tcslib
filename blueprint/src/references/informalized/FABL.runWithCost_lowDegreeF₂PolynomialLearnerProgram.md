<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.runWithCost_lowDegreeF₂PolynomialLearnerProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low-degree learner run law

**Claim.** The low-degree polynomial learner’s run law is obtained by drawing a uniform batch of $m$ cube inputs, evaluating the target on each, returning the learner’s output on those labeled samples, and charging cost $(m,0,m+W)$, where $W$ is the work on that batch.

**Proof.** Unfold the learner, whose first operation draws $m$ independent uniform cube inputs. For each resulting batch, the continuation charges the learner’s specified work and returns its low-degree hypothesis computed from the corresponding labeled samples $(x_i,f(x_i))$. By the definition of the run law, drawing the batch contributes $m$ random examples and $m$ units of work; the tick adds the batch-dependent work $W$. The pure return leaves the output unchanged. Hence the law is the uniform input-batch law mapped to the stated output and total cost.
