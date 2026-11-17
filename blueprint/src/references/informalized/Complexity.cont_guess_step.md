<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_guess_step -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Step of the Guessing Phase

**Claim.** From the invariant configuration for $(d,u)$, one guessing-phase step under bit $b$ gives the invariant configuration for the successor of $d$, with $b$ appended to $u$ exactly when the simulated machine emits an output symbol.

**Proof.** First separate the case where $d$ is already halted. The simulated machine then stays put and emits nothing (`Turing.MultiTapeTM.step_of_halt`); the guessing machine’s halt-control transition also leaves the represented data unchanged. Its zero input movement preserves the input position (`Turing.moveInputPos_zero`). Now suppose $d$ is active and let $a$ be its transition action. The invariant configuration presents the same input symbol and original work-tape symbols as $d$, so the guessing machine uses this same action, except that any emitted symbol is replaced by the supplied choice bit and written to the extra capture tape. The original work tapes and their head movements therefore match the successor of $d$. If the action emits, the capture head is at the end of $u$; writing $b$ there changes the buffer to $u b$ (`Turing.FinTM.bufferTape_append`), while the capture head advances accordingly. If it does not emit, both buffer and head remain unchanged. In either case no symbol is added to the output tape, so the resulting fields are exactly those of the asserted invariant configuration.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.moveInputPos_zero`, `Turing.FinTM.bufferTape_append`.
