<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearningAlgorithm.lean :: FABL.lowDegreeJuntaLearningAlgorithm_successProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Success of the Low-Degree Junta Learner

**Claim.** For a Boolean function that is a $k$-junta, the low-degree junta learning algorithm outputs a hypothesis whose relative Hamming distance from the target is at most the requested accuracy with probability at least $9/10$.

**Proof.** Let $B$ be the event that the recursive junta learner produces a bad output, and let $A$ be the event that the hypothesis obtained from its output has relative Hamming distance at most the requested accuracy. For every possible output, either it is bad or it gives an accurate hypothesis: this is precisely the implication that a nonbad output is accurate (\texttt{lowDegreeJuntaHypothesisOfOutput_accurate_of_not_bad}). Thus these two events cover all outcomes. The event-cover inequality (\texttt{one_le_eventProbability_add_of_output_cover}) says their probabilities sum to at least $1$. Since the target is a $k$-junta, the learner's failure bound (\texttt{lowDegreeJuntaLearnerProgram_failureProbability_le}) gives $\Pr(B)\le 1/16$, using the algorithm's chosen failure parameter. Consequently, $\Pr(A)\ge 1-1/16=15/16$, which is at least $9/10$. Finally, the algorithm reports the hypothesis obtained by mapping the recursive learner's output through the hypothesis conversion. Mapping an output preserves the probability of any event defined in terms of that mapped output (\texttt{eventProbability_map_output_eq}); hence the same accuracy probability bound holds for the learning algorithm itself. The requested accuracy affects the definition of accuracy in the event, while the learner's fixed failure parameter supplies the stated probability guarantee.

**Key facts.** `FABL.one_le_eventProbability_add_of_output_cover`, `FABL.lowDegreeJuntaHypothesisOfOutput_accurate_of_not_bad`, `FABL.lowDegreeJuntaLearnerProgram_failureProbability_le`, `FABL.eventProbability_map_output_eq`.
