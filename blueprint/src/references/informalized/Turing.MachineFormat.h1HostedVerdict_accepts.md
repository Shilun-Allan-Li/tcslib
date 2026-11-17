<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.h1HostedVerdict_accepts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hosted machine verdict

**Claim.** Under the stated representation and live-entry hypotheses, the hosted verdict machine halts within the specified time bound and appends a bit that is true exactly when the decoded machine halts on $x$ within $t$ steps with output $[1]$.

**Proof.** Apply the hosted-verdict effect theorem to the decoded machine and the given represented initial configuration. It supplies a time within the required bound at which the hosted machine has halted and has appended the machine’s time-$t$ summary bit to the existing output. The summary-clock acceptance theorem identifies that bit as true exactly when the machine computes output $[1]$ on $x$ within $t$ steps. Taking this summary bit as the answer gives the required output and equivalence.

**Key facts.** `Turing.MachineFormat.h1HostedVerdict_effect`, `Turing.MachineFormat.summaryClock_accepts`.
