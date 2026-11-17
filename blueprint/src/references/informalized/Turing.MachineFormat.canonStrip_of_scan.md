<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonStrip_of_scan -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical prefix from a successful scan

**Claim.** If scanning $\alpha$ succeeds and returns $tail$, then removing the trailing ones from $\alpha$ gives the serialization of the code decoded from $\alpha$.

**Proof.** A successful scan returns a suffix consisting entirely of ones (`canonScan_all`). By the scan-to-full-parse identity (`scan_full`), the same successful parse yields a code $M$ and suffix $tail'$, and the decoder returns $M$. The soundness of full parsing (`parseFull_sound`) then gives $\alpha=F.serialize(M)++tail'$. Every serialization in this format ends in a zero; hence it can be written $u++[false]$ (`serializeK_last`, together with the format's serialization equation). Removing trailing ones from $\alpha$ therefore removes exactly $tail'$ and leaves $F.serialize(M)$, by the trailing-one removal identity (`canonStrip_append`). Since the decoder's value is $M$, this is the claimed serialization.

**Key facts.** `Turing.MachineFormat.canonScan_all`, `Turing.CodeFormat.scan_full`, `Turing.CodeFormat.parseFull_sound`, `Turing.MachineFormat.serializeK_last`, `Turing.MachineFormat.canonStrip_append`.
