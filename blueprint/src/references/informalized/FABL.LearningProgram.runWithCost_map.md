<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.runWithCost_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Law Under Output Mapping

**Claim.** Running a program with its output mapped by $f$ has the same law as mapping each run's output by $f$ while leaving its learning cost unchanged.

**Proof.** By definition, mapping an output binds the program to the continuation that returns the image under $f$. The cost law for binding (`runWithCost_bind`) expresses this as first running the original program and then running that pure continuation, adding the original cost. Since the continuation is pure, it changes only the output and incurs zero additional cost. Thus the resulting law is precisely the original run law mapped by $(a,c)\mapsto(f(a),c)$.

**Key facts.** `FABL.LearningProgram.runWithCost_bind`.
