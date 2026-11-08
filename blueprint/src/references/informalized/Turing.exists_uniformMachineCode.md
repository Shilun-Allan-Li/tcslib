<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Turing.exists_uniformMachineCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform machine code

**Claim.** There exists an effective code for finite-state deterministic Boolean machines, together with a finite-state Boolean simulator and a natural-number degree, satisfying the stated bounded acceptance and rejection guarantees, padding-invariant decoding, and timed canonical serialization.

**Proof.** Take the code whose encoder serializes a machine and whose decoder is the total decoder from the machine-format construction. Its padding property is supplied by the serialization-padding theorem. The polynomial canonizer theorem gives a machine computing the serialization of every decoded code, with time bound of the required form; use its coefficient as the canonizer degree and define the canonizer time function accordingly. The uniform-simulator theorem gives one simulator and one degree that decide bounded acceptance on the paired input, outputting true when the decoded machine accepts in the specified time and false otherwise. Package these machines, bounds, and properties into the effective uniform code structure.

**Key facts.** `Turing.MachineFormat.exists_polyCanonizer`, `Turing.MachineFormat.exists_uniformSimulator`, `Turing.codeDecode_serialize_pad`.
