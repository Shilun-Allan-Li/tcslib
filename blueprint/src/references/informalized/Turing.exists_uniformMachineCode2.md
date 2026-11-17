<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Codes2Tape.lean :: Turing.exists_uniformMachineCode2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two-tape uniform machine code

**Claim.** There exists an effective code for two-work-tape deterministic Boolean machines, with a finite-state Boolean simulator and a degree giving the stated polynomial-time bounded acceptance and rejection guarantees, along with padding-invariant decoding and timed canonical serialization.

**Proof.** Use the two-tape format's polynomial-time canonizer and uniform simulator. The canonizer computes the serialization of the decoded machine within its polynomial bound, and the simulator decides whether that machine outputs true in exactly the specified time, returning true in the positive case and false otherwise within its uniform polynomial budget. Choose the two-tape serialization as the encoder and the format's decoder as decoder; the serialization-padding theorem gives the required invariance under appending true bits. These data and their bounds form the required nonempty code structure.

**Key facts.** `Turing.MachineFormat.exists_polyCanonizer`, `Turing.MachineFormat.exists_uniformSimulator`, `Turing.CodeFormat.decode_serialize_pad`.
