<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridge_emit_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Emission Step

**Claim.** When the main stack begins with the bit symbol for $b$, the bridging machine removes that symbol in one step, enters the emitting state with pending bit $b$, leaves the input-head position and other stacks unchanged, and appends the previous pending bit to the output if present.

**Proof.** The configuration’s main-stack head symbol is the bridge-alphabet embedding of the first stack symbol, by the stack-reading fact (`bridgeCfg_read`). Under the hypothesis that this symbol is the bit encoding of $b$, the emitting transition therefore takes the corresponding bit branch. In either Boolean case, that transition pops the main-stack head, moves its work head to the next stack position, records $b$ as the pending bit, and appends the old pending bit to the output when it exists. The stack-pop update fact (`bridgeCfg_pop_emit`) identifies the resulting configuration; the machine-step description (`bridge_step`) connects this transition with the actual one-step evolution. The two cases $b=	ext{false}$ and $b=	ext{true}$ yield the stated result.

**Key facts.** `Turing.bridgeCfg_read`, `Turing.bridgeCfg_pop_emit`, `Turing.bridge_step`.
