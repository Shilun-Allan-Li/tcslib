<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalInterpreter.lean :: Turing.universal_serialization_header -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Header and Remaining Record Table

**Claim.** For every machine in code normal form, there is a bit string of records such that its canonical serialization is the pair encoding of the binary digit string of its state-count parameter with the unary initial-state code followed by the records.

**Proof.** Choose the remaining record string to be the machine's transition records. Expanding the serialization shows that its second component consists of the unary code for the initial state, the delimiter bit $0$, and those records. Associativity of list concatenation places this in the required form, and applying the pair encoding to equal second components gives the asserted serialization identity.
