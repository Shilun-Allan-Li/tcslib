<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopReady_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Prepared Startup

**Claim.** For any fuel configuration, the prepared startup configuration equals the startup call on the initial configuration of the body machine, with release clear, no flag, counter word equal to the fuel output, and fuel configuration unchanged.

**Proof.** Compare the configuration fields. The state and input-head position agree directly. For the work tapes, separate the last tape from the preceding tapes, then split those preceding tapes into the body tapes, the flag tape, and the fuel tapes. On body tapes, both configurations contain the blank work tapes of the body's initial configuration. On the flag tape, both have no symbol stored; on the counter tape, both store the fuel output starting at cell zero; and on the fuel tapes, both retain the given fuel configuration. The final payload tape is blank in both configurations. The work-head positions agree as well: body and flag heads are at zero, the counter head is at zero, payload head is at zero, and the fuel heads are those of the given configuration. The outputs are both empty. These componentwise equalities establish equality of configurations.
