<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.emCall_layout_pair -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values at argument and capture slots

**Claim.** At either role's physical index in the call layout, the layout value is the assigned argument value for the argument role and the assigned capture value for the capture role.

**Proof.** There are two roles. At the argument role, the physical index is $0$, the first slot of the layout, where the value is assigned to be $\mathrm{arg}$. At the capture role, the physical index is the final slot, where the value is assigned to be $\mathrm{cap}$. Evaluating these two cases gives the claimed conditional value.
