<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeSimulator.lean :: Turing.MachineFormat.canonEmbedWords -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Word Configuration Equality

**Claim.** If the wanted tape words agree with the smaller machine’s words on embedded indices, and the ambient words agree with the wanted words outside the embedding, then embedding the smaller word configuration using the ambient words and zero auxiliary head positions gives the wanted word configuration.

**Proof.** Use the configuration equality criterion of `Turing.MachineFormat.canonEmbedEq`. The state and input position agree by construction, as does the output, since both output prefixes are empty. On an embedded index, the embedded tape stores the smaller tape’s word; the selected-word hypothesis says that word is the wanted one. The head position is zero on both sides. Outside the embedding, the supplied ambient word equals the wanted word, so their tape contents agree, and both head positions are zero. These componentwise agreements meet the criterion and give the claimed configuration equality.

**Key facts.** `Turing.MachineFormat.canonEmbedEq`.
