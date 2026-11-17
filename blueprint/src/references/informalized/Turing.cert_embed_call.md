<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_embed_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Machine Call

**Claim.** The embedded machine reproduces the original run’s final configuration on the larger tape set, with the specified final tape words, and avoids the exit state at every earlier time.

**Proof.** First identify the larger initial configuration with the embedding of the local initial configuration: on embedded tapes the words agree by the input-word hypotheses, and on the remaining tapes the framing words are unchanged. The run-transport property for the embedded machine then says that at every time its configuration is the embedding of the original machine’s configuration at that time. At time $t$, the original run reaches the exit state and local final words; the output-free embedding converts this into the larger final assignment, using the specified agreement on embedded tapes and the unchanged words outside their image. Finally, at each $u<t$, transport identifies the embedded state with the original state, which is not the exit state by hypothesis.

**Key facts.** `Turing.cert_embed_words`, `Turing.embedEmitTM_runFrom`.
