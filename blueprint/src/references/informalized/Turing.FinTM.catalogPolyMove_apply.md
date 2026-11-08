<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogPolyMove_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a Head-Only Move

**Claim.** Applying an action that moves only head $i$ by direction $d$ and enters state $s'$ preserves the input, tape contents, and output, changes the state to $s'$, and changes only head position $i$, by adding $d$.

**Proof.** Compare the configuration fields after applying the action. The state is set to $s'$ by the action, and the input head is unchanged because the input movement is zero (Turing.moveInputPos_zero). No tape cell is written, so every tape's contents are preserved, and the output is unchanged because the action emits no symbol. For each work-tape head position, the action adds its designated movement: this is $d$ at index $i$ and zero at every other index. Thus the new position function is precisely the old one updated at $i$ with value $h(i)+d$.

**Key facts.** `Turing.moveInputPos_zero`.
