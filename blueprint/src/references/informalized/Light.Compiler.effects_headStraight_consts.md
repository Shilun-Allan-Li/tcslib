<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/StartUp.lean :: Light.Compiler.effects_headStraight_consts -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialized Constant Cells

**Claim.** For every word size and initial memory, executing the three-instruction head-initialization sequence leaves the cells at addresses $-5$, $-7$, and $-9$ holding the word representations of $1$, $0$, and $-1$, respectively.

**Proof.** The preceding description of the sequence's effect expresses the final memory as three successive updates: first write $1$ at $c_{\mathrm{ONE}}$, then $0$ at $c_{\mathrm{ZERO}}$, then $-1$ at $c_{\mathrm{NEG}}$. Reading each updated address returns the value written there, by the defining property of function update. Hence all three asserted cell values hold.

**Key facts.** `Light.Compiler.effects_headStraight`.
