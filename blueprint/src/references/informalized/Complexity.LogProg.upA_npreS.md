<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathMachine.lean :: Complexity.LogProg.upA_npreS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Safety Invariant for the Program

**Claim.** For every Boolean input and abstract configuration, the stated safety condition holds: live equality tests use distinct registers, input comparisons occur only on inputs with the required canonical encoding, and calls have argument lists without repetitions. No restriction is imposed in the other states.

**Proof.** Unpack the abstract configuration. If its control state is halted, the safety condition is true by definition. For a live state, inspect the instruction assigned by the program at that state. Instructions other than register equality tests, input comparisons, and calls impose no condition. For each ordinary equality test, the two register indices are distinct, as is checked directly from the program's finite list of cases. At each comparison with the first payload or either payload of a nested encoding, the designated state is reached only under the corresponding valid-input condition, which is exactly the requirement in the invariant. Finally, each call uses a one-element argument list, which has no repetitions. These checks cover all live states, including the nondeterministic choice states, where the condition is vacuous.
