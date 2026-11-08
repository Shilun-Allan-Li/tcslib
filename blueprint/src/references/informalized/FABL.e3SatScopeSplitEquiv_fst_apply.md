<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSP.lean :: FABL.e3SatScopeSplitEquiv_fst_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Assignment on the Constraint Scope

**Claim.** For a Boolean assignment and a three-literal satisfiability constraint with scope $c$, the first component of the scope/off-scope assignment split is the function $i\mapsto a(c_i)$.

**Proof.** The first component of the split is obtained by restricting the assignment to the range of the scope embedding, then transporting that restriction back along the scope embedding, whose target is precisely that range. Evaluating this transported function at a position $i$ first maps $i$ into the range and then takes its unique preimage in the scope. The resulting variable is exactly $c_i$, so the value is $a(c_i)$.
