<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_statement -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation of One Stack-Machine Step

**Claim.** For any supported compiled statement, optional register value, and stack assignment, the bridging machine reaches in finitely many steps the configuration encoding the result of one stack-machine step, while preserving the input position and output.

**Proof.** Proceed by induction on the statement, keeping the register and stack assignment arbitrary. In each case, the bridge configuration encodes each stack as a work tape and places its head at the top of that stack; its input position and output are carried along unchanged.

1. For a push, the bridge first moves the relevant tape head to make room, then writes the encoded pushed symbol. The two transitions therefore encode the updated stack and pass control, with the unchanged register, to the tail. The tail remains in the compilation support by closure under immediate substatements (`Turing.bridge_sub`), so the induction hypothesis completes the simulation. Concatenating these finite runs gives the result (`Turing.bridgeReach_trans`).
2. For a peek, the bridge reads the top symbol and passes its decoded value to the continuation in one transition. The read agrees with the stack head (`Turing.bridgeCfg_read`), and an idle action changes only the control state (`Turing.bridgeCfg_idle`). The tail is supported, so the induction hypothesis applies. For a pop, it likewise reads the top symbol for the continuation and removes it from the encoded stack; the tape update realizes precisely the tail of the stack, including the empty-stack case (`Turing.bridgeCfg_pop_any`). The induction hypothesis then simulates the tail.
3. For a load, a single idle transition passes the updated register to the tail without changing stacks. For a branch, evaluate the Boolean test: the bridge selects the corresponding yes or no continuation, and the induction hypothesis applies to that supported substatement. In each case the one-step transition reaches the appropriate intermediate configuration, after which the tail simulation finishes.
4. For a goto, one idle transition transfers control to the translated target statement, with the register and stacks unchanged. For halt, one idle transition transfers control to the absent statement and leaves the register and stacks unchanged. These are exactly the results of the respective stack-machine steps.

To identify each transition with its action on the encoded configuration, use the one-step unfolding of the bridge machine (`Turing.bridge_step`). The finite-run calculations use the facts that a run of length zero is the initial configuration and a run of length one more is one step after the shorter run (`Turing.MultiTapeTM.runFrom_zero`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`). The bridge state's encoding is available whenever its statement belongs to the support (`Turing.bridgeExec_mem`).

**Key facts.** `Turing.bridge_sub`, `Turing.bridgeReach_trans`, `Turing.bridgeCfg_push`, `Turing.bridgeCfg_read`, `Turing.bridgeCfg_idle`, `Turing.bridgeCfg_pop_any`, `Turing.bridgeExec_mem`, `Turing.bridge_step`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.MultiTapeTM.runFrom_zero`.
