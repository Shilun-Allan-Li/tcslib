<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/Program.lean :: FABL.LearningProgram.runWithCost_bind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost Law for Program Sequencing

**Claim.** The law of running a program formed by binding a continuation to an original program equals the law obtained by first running the original program and then running the continuation on its output, adding the two learning costs.

**Proof.** Induct on the structure of the original program. In the pure case, binding simply runs the continuation on the fixed output, and adding the zero initial cost leaves its law unchanged. For each random choice constructor—coin, single example, example batch, uniform-input batch, and example matrix—the induction hypothesis identifies the continuation law for every sampled choice. Associativity of probability-law bind then puts the two stages in sequence, while `bind_map_addOutcomeCost_comm` shows that the constructor's fixed cost charge can be moved to the final outcome and combined with the continuation's cost. A query has a fixed answer, so the same argument applies to the branch selected by that answer. A tick likewise contributes a fixed cost, handled by the same commutation fact. In the matrix-output case, the bound continuation first charges the specified work after computing the matrix output; combining this with the matrix sampling charge gives the declared total matrix cost, using associativity of cost addition. These cases establish the sequencing law for every program.

**Key facts.** `FABL.LearningProgram.bind_map_addOutcomeCost_comm`, `FABL.LearningProgram.map_addOutcomeCost_zero`.
