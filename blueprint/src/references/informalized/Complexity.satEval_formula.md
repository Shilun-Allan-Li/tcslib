<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satEval_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Evaluation Pass

**Claim.** For a CNF formula with variable indices covered by the certificate word, the evaluator processes the doubled formula serialization in at most three times its length, halts, and outputs the single bit given by the incoming formula bit conjoined with the formula's truth value.

**Proof.** Induct on the formula. For the empty formula, the serialization is its terminal delimiter. The canonical input-symbol rule (`Complexity.satEvalCfg_input`) identifies that bit as false; one evaluator step halts and outputs the incoming bit. This is the required value because the empty CNF evaluates to true.

For a formula consisting of a clause $C$ followed by a formula $\varphi$, split the doubled serialization into the doubled formula marker, the doubled serialization of $C$, and the doubled serialization of $\varphi$. The head clause inherits the variable-index bound, as does the tail formula. First, the two-step doubled-bit rule (`Complexity.satEval_double`) processes the marker and moves into clause phase. The clause-pass result (`Complexity.satEval_clause`) processes $C$, returning to formula phase with formula bit $a\wedge C(u)$. Then apply the induction hypothesis to $\varphi$ with this bit. The run concatenation law (`Turing.MultiTapeTM.runFrom_add`) joins these three stages. The recursion for CNF evaluation identifies the final output as $a\wedge(C(u)\wedge\varphi(u))$, and the serialization-length calculation gives the stated bound of three times the full serialization length.

**Key facts.** `Complexity.satEvalCfg_input`, `Complexity.satEval_double`, `Complexity.satEval_clause`, `Turing.MultiTapeTM.runFrom_add`.
