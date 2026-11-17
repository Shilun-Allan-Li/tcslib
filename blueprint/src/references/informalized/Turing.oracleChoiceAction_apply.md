<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/OracleSim.lean :: Turing.oracleChoiceAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Applying a lifted action

**Claim.** Applying the lifted action to the lifted configuration, even when its state has been replaced by an arbitrary optional state $s$, produces the lifted configuration of the original action's result, retaining the added tape contents and moving its head from $p$ to $p+1$.

**Proof.** Compare the configuration fields. The state, input-head position, and output agree directly from the definitions: the lifted action uses the original action's input movement and output, and the state override affects only the starting state, which the action replaces with its own successor state. For work tapes, separate the added slot from all other slots. At the added slot the action makes no write and moves the head one cell right, so its contents remain $tape$; at every other slot, insertion of the extra slot recovers the corresponding original tape and action, giving precisely the tape update prescribed by applying $a$ to $c$. The same separation for head positions shows the added head becomes $p+1$, while every original head moves by the original action's displacement. These fieldwise agreements establish the claimed configuration equality.
