<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/StraightLineDualRail.lean :: BoolCircuit.StraightLine.emitOp_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of Operation Emission

**Claim.** Emitting a conjunction or disjunction from at most two argument rails preserves statement validity, emits at most two statements, returns rails with valid references, and makes those rails evaluate to the gate value and its complement whenever the argument rails evaluate to their respective values and complements.

**Proof.** Separate the cases according to the number of arguments.

With no arguments, emission creates two statements using the chosen input coordinate and its negation, with the dual operation on the first statement and the requested operation on the second. The appended statements are valid because their operands are inputs. Their two new lines evaluate to the operation's value and its complement: checking the two possible operations and the two Boolean values of the chosen input verifies the claim. The resulting rail references those two new lines, which lie within the extended statement list.

With one argument, emission returns that argument's rail pair and adds no statements. The assumed evaluation property of the referenced pair therefore gives the result directly. Its references remain valid, and the original statement list remains valid.

With two arguments, emission appends two statements: the requested operation on the first rails, then its dual on the complementary rails. The existing references are valid in the old list; hence they remain valid after appending the statements. The first new statement is valid at the old list length, and the second is valid at the next position, so the extended list is valid. The output rails refer to these two new lines. When the extended list is evaluated, its new lines are the two statement values appended to the old evaluation (`runLines_two`); references to old lines keep their values when the evaluation list is extended (`SLOperand.eval_append`). Thus the first output is the requested operation applied to the two argument values, and the second is its complement, by the Boolean duality of conjunction and disjunction. In every case the number of emitted statements is at most two.

**Key facts.** `BoolCircuit.StraightLine.LinesValid.snoc`, `BoolCircuit.StraightLine.length_runLines`, `BoolCircuit.StraightLine.runLines_two`, `BoolCircuit.SLOperand.eval_append`.
