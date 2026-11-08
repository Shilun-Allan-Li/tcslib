<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogPolyMove_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work Tape Head Movement

**Claim.** Applying the action that keeps the input head fixed, leaves tape contents and output unchanged, moves only the selected work-tape head by $d$, and sets the control state to $s'$, yields the stated updated configuration.

**Proof.** Compare the resulting configuration component by component. Its state is $s'$ by the action definition. The input head stays in place because moving it by zero leaves its position unchanged (`moveInputPos_zero`). The work-tape contents are unchanged, since the action specifies no writes. For the head positions, the selected head moves by $d$ and every other head has movement zero; this is exactly the function obtained by replacing $h(i)$ with $h(i)+d$. The output is unchanged because the action emits no symbol. All components therefore agree with the claimed configuration.

**Key facts.** `Turing.moveInputPos_zero`.
