<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/TMSAT.lean :: Complexity.tmsat_pt_unary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# All-ones test is polynomial-time computable

**Claim.** The function returning the one-bit word whose bit is $1$ exactly when every bit of $x$ is $1$ is polynomial-time computable, including on the empty word.

**Proof.** Incrementing a fixed-width word and replacing failure by the empty word is a linear-time computable function (`Turing.FinTM.computesFunInTime_incFixed`, together with `Complexity.polyTimeComputable_of_linear`). The increment is undefined exactly for the all-ones word, including the empty word (`Complexity.tmsat_inc_none`). When it is defined, its output is nonempty (`Complexity.tmsat_inc_nonempty`). Consequently, replacing an undefined result by the empty word yields the empty word exactly on all-ones inputs: a defined increment cannot have empty output. Testing whether this result equals the empty word is polynomial-time computable (`Complexity.tmsat_pt_eq`). Composing that test with the linear-time computation preserves polynomial-time computability (`Complexity.PolyTimeComputable.comp`). The resulting equality test returns $[1]$ precisely for all-ones inputs, as required.

**Key facts.** `Turing.FinTM.computesFunInTime_incFixed`, `Complexity.polyTimeComputable_of_linear`, `Complexity.PolyTimeComputable.comp`, `Complexity.tmsat_inc_none`, `Complexity.tmsat_inc_nonempty`, `Complexity.tmsat_pt_eq`.
