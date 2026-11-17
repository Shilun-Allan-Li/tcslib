<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.pathA_npreS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Path Program Precondition

**Claim.** For every input and abstract configuration, the precondition holds for the program obtained from `pathA` by replacing each choice instruction with the answer “no”.

**Proof.** If the control label is absent, the precondition holds by its definition. For a present label, inspect the finitely many instructions in `pathA` after replacing each choice instruction by its negative-answer return. The only nontrivial requirements are that the two registers in each equality comparison be distinct and that the argument list at each oracle call have no repetitions. The listed comparisons use distinct register indices, and every listed call has the singleton argument list `[0]`, which has no repetitions. No instruction in this program requires one of the input-format conditions, so those cases impose no additional assumption. All remaining instruction cases have a precondition that holds automatically.
