<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Simulation.lean :: Light.Compiler.Start.room_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stack room at the next depth

**Claim.** Under the start conditions and the bound $d<S.\mathrm{lim}.\mathrm{depth}$, the stack has enough room for the current frame together with the allocation required at depth $d+1$.

**Proof.** The start condition gives $q+S.F+(S.F+1)(S.\mathrm{lim}.\mathrm{depth}-d)\le S.Q$. Since $d<S.\mathrm{lim}.\mathrm{depth}$, the natural-number difference satisfies $S.\mathrm{lim}.\mathrm{depth}-d=S.\mathrm{lim}.\mathrm{depth}-(d+1)+1$. Expanding the product over this successor rewrites the left side as $q+S.F+(S.F+1)(S.\mathrm{lim}.\mathrm{depth}-(d+1))+(S.F+1)$. This is exactly the desired left side, because $S.F+1+S.F=S.F+1+S.F$; the inequality follows by rearranging the natural-number terms.
