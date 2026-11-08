<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Bidirectional.lean :: Turing.FinTM.foldStartAction_embed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Start Action on Embedded Symbols

**Claim.** For every alphabet $\Gamma$, state type $S$, number $k$ of work tapes, state $q\in S$, and possibly absent symbol $x\in\operatorname{Option}(\Gamma)$, the guarded start action on the image of $x$ under the alphabet embedding equals the initialization action toward $q$.

**Proof.** If $x$ is absent, mapping it through the embedding leaves it absent, and the start action is defined to be the initialization action. If $x$ is present, its embedded folded symbol has the form $(\mathrm{false},\mathrm{some}\ x,\mathrm{none})$, which decodes to $x$. The start action therefore takes its successful-decode branch, which is again the initialization action.
