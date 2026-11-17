<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Host_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulating a Machine Call in the Host

**Claim.** When module $i$ has at least one work tape, starts in its initial state on the given argument, runs without halting before time $t$, and halts at time $t$ with the stated result and output, the host simulation avoids its loop anchor before time $t$ and at time $t$ reaches the resolved return state with the result on tape zero and the prior output prefix followed by the module output.

**Proof.** Let $c$ be the called machine’s initial configuration with the argument on tape zero. Embed its states into the host’s module-$i$ state component, and pad its configuration to the host’s $K$ work tapes. The initial host configuration is exactly the emitted, padded version of $c$ (`Complexity.clA5Host_seam`). Up to time $t$, the host’s transition rule on embedded states agrees with the called machine’s transition rule after padding; the called machine remains live at every earlier time by hypothesis. The simulation theorem for emitted machines therefore identifies the host configuration at every $v\le t$ with the emitted, padded called-machine configuration at time $v$ (`Turing.emit_run`), and the padding identity gives the corresponding unpadded run (`Complexity.clA5Pad_run`). For each $v<t$, the called machine is not halted, so its state is some ordinary state; after embedding, the host state remains in the module component and cannot be the loop anchor. At time $t$, use the assumed halted configuration. Emission maps its halted state to the resolved return state and concatenates the existing output prefix with the called machine’s output; the seam identity (`Complexity.clA5Host_seam`) then gives exactly the claimed host configuration.

**Key facts.** `Complexity.clA5Host_seam`, `Complexity.clA5Pad_run`, `Turing.emit_run`.
