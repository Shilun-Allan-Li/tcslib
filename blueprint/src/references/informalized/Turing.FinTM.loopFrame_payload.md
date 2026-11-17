<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopFrame_payload -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payload Head Read

**Claim.** For any two Boolean finite Turing machines and the specified loop-host data, the symbol scanned on the payload track in the resulting controller frame is the value of the payload tape at the payload-head position.

**Proof.** The last work tape is precisely the payload track: its index is `Fin.last (body.k + 1 + (1 + F.k))`. This index is distinct from the flag-track index `body.k`, since the last index is strictly larger. Thus the frame definition assigns the payload tape to this track, while its head position is assigned to `ph`. Evaluating the scanned symbol at that head therefore gives `payload ph`.
