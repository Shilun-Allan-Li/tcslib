<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_setup -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Non-forward simulator setup

**Claim.** For every Boolean word $x$, the non-forward simulator reaches within $5(|x|+1)$ steps the virtual initial configuration determined by decoding $x$; if decoding fails, it is halted with empty output.

**Proof.** Apply the parsing lemma `a2_map_parse` to the whole input, with empty prefix, empty previously accumulated buffer, and empty output prefix. It gives a time at most $3|x|+5$, hence at most $5(|x|+1)$, and the claimed result according to whether decoding succeeds. The simulator’s actual initial configuration is the parsing configuration with input head at position $1$ and blank tapes; this is exactly the parsing lemma’s starting configuration when the accumulated buffer and output are empty. Substituting that identification gives the desired run from the initial configuration. In the successful case, the accumulated word is the decoded first component, the virtual machine is initialized on the decoded second component, and the output is the encoding of the first component paired with the empty word. In the failure case, the parsing lemma already gives a halted configuration with empty output.

**Key facts.** `Turing.FinTM.a2_map_parse`.
