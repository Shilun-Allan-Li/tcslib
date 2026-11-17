<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineSetup.lean :: Complexity.Meyer.tabTM_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Tabulation Machine Setup

**Claim.** If parsing the input fails, the tabulation machine halts with output $[\mathrm{false}]$ within $|y|+1$ steps. If parsing succeeds, it reaches the specified decoding configuration within $2|y|+4$ steps.

**Proof.** Split first on whether the selector field fits within the input, that is, whether $nbits(M)\le |y|$.

If it does not fit, the selector-rejection result gives a halting run with output $[\mathrm{false}]$ after $|y|+1$ steps (`Complexity.Meyer.sel_reject`). If it does fit, the machine first scans the selector bits (`Complexity.Meyer.sel_done`), reaching the field-reading state. If the first field cannot be read, the field-failure result produces the rejecting halt; if the first field is read but the second is not, the field-reading result processes the first field and then the failure result rejects on the remainder (`Complexity.Meyer.field_none`, `Complexity.Meyer.field_some`). In each case the parse-failure hypothesis identifies the applicable parsing failure, and composing the runs uses the run-addition law (`Turing.MultiTapeTM.runFrom_add`). The conversion from the intermediate configuration with empty list tapes to the stated auxiliary-tape configuration is exactly the empty-tape identification (`Complexity.Meyer.pcfg_nil`). The field lengths and parsing equations bound these steps by $|y|+1$.

Now suppose parsing succeeds with fields $bits,t,a,x$. Unfolding the parser identifies the two successful field reads and their outputs. The read-field decomposition writes each encoded field as its code followed by a delimiter and the remaining suffix (`Complexity.Meyer.readField_eq_some`). These decompositions give the input length as $nbits(M)+2|t|+2|a|+4+|x|$ and identify the successive suffixes consumed by the machine.

The selector scan and first-field scan reach the state for parsing the second field (`Complexity.Meyer.sel_done`, `Complexity.Meyer.field_some`). The second-field scan reaches the copying state (`Complexity.Meyer.field_some`), and the copy run transfers $x$ to its auxiliary tape (`Complexity.Meyer.cpy_run`). The three rewind results then place the heads at cell zero and advance through the rewind, rewind, and decoding states, respectively (`Complexity.Meyer.rewX_run`, `Complexity.Meyer.rewC_run`, `Complexity.Meyer.rewO_run`). Chaining these configuration equalities with the run-addition law yields precisely the requested decoding configuration, with the input head at the right boundary, the three buffers holding $x,t,a$, the other tapes blank, and output empty. Finally, the displayed input-length identity and elementary bounds on the field lengths show that the total number of steps is at most $2|y|+4.

**Key facts.** `Complexity.Meyer.sel_reject`, `Complexity.Meyer.sel_done`, `Complexity.Meyer.field_none`, `Complexity.Meyer.field_some`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.Meyer.pcfg_nil`, `Complexity.Meyer.readField_eq_some`, `Complexity.Meyer.cpy_run`, `Complexity.Meyer.rewX_run`, `Complexity.Meyer.rewC_run`, `Complexity.Meyer.rewO_run`.

**Caveat.** The proof uses several field-scanning and copying run lemmas whose full inductive proofs are not included in the supplied upstream statements; their stated run effects are followed directly here.
