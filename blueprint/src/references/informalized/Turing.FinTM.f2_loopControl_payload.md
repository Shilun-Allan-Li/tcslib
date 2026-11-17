<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_loopControl_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Loop Control Payload Action

**Claim.** The loop-control action that moves only the payload head by $d$, leaves the payload unchanged, and produces the specified output and next state is the right-block extension of the corresponding one-tape action.

**Proof.** The input movement, output, and next state agree immediately on both sides. For the work tapes, the right-block extension assigns blank stationary actions to the added block and uses the one-tape action on the final block. Its first block therefore agrees with the loop-control action, which leaves the flag and counter unchanged. On the final block, its sole tape is the payload tape and has action $(\mathrm{none},d)$; all other tapes in that block are blank and stationary. Thus the work-tape actions agree at every index, proving equality of the actions.
