<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.codeCanonical_machine -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Machine computing canonical serialization

**Claim.** There are a finite Turing machine over the Boolean alphabet and a time bound depending only on input length such that, on every Boolean input, the machine halts at that time and outputs the serialization of the machine decoded from the input.

**Proof.** The one-tape format has a primitive-recursive table-skipping procedure, supplied by `codePrimSkipTable1`. The general canonizer existence theorem (`CodeFormat.exists_canonizer`) says that any code format with such a procedure admits a finite machine and a length-dependent time function computing the serialization of the decoded input. Apply it to the one-tape format. Its output is the serialization of the decoded machine, as required.

**Key facts.** `Turing.codePrimSkipTable1`, `Turing.CodeFormat.exists_canonizer`.
