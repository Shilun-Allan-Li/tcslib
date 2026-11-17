<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.macroCfg_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Macro Configuration Action

**Claim.** The specified read-only schedule action sends the macrostep configuration determined by $B,q,u,g$ to the one determined by $B,q',u+d_u,g+d_g$.

**Proof.** Compare the configuration fields. The action sets the state to $q'$, leaves the input head in place by the zero-move identity (`Turing.moveInputPos_zero`), and emits no output, so the appended output list is unchanged. It makes no changes to the original work tapes or the budget head. The three added work tapes are the budget, unary counter, and guide tapes; their head positions are respectively unchanged, shifted by $d_u$, and shifted by $d_g$. For the last two positions, the finite index has only the possibilities $0,1,2$ (`Complexity.finThree_cases`), which verifies the corresponding cases in the definition of the macro configuration. These field equalities establish the claimed configuration equality.

**Key facts.** `Turing.moveInputPos_zero`, `Complexity.finThree_cases`.
