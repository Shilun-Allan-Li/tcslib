<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.lenAction_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Administrative action on a checker configuration

**Claim.** Under the given head-movement and position equations, the administrative action sends the checker configuration indexed by $c,q,i,r$ to the one indexed by $c,q',j,s$, with output equal to the optional bit's list.

**Proof.** Compare the configuration fields. The action sets the successor state to $q'$, and the assumed input-head movement equality gives the new input position $j+1$. The action does not write to the original $M.k$ tapes, so their contents remain those of $c$; their head positions are unchanged as well. For the extra tape, its head starts at $r-1$ and moves by $d$, which equals $s-1$ by hypothesis. Thus the resulting tape-head positions and all tape contents agree with the checker configuration indexed by $c,q',j,s$. The output field is the list represented by the optional bit $b$, as asserted.
