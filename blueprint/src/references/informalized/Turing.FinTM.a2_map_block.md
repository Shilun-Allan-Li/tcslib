<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.a2_map_block -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an aligned bit pair

**Claim.** After reading two consecutive input bits, the simulator appends them to the first buffer and returns to parsing when they agree; when they differ, it halts if the first bit is true and enters the copy state with the first-buffer head moved one position left if the first bit is false. The input head advances by two, while the second buffer and output stay empty.

**Proof.** First, the one-step parsing rule reads $b$ and stores it as the pending bit, advancing the input head to the position of $c$; this is the first-bit transition (`a2_map_first`). The input-reading property of configurations (`a2_mapCfg_read`) identifies the symbol at that position as $c$. The second parsing transition therefore compares $b$ and $c$. If they agree, it writes $b$ at the end of the first buffer and returns to parsing; the fact that appending a bit to a buffer is exactly a write at its old length (`bufferTape_append`) gives the resulting buffer $a\mathbin{++}[b]$. If they differ and $b$ is true, the transition enters the halting state without changing either buffer or head position. If they differ and $b$ is false, it enters the copy state and moves the first-buffer head left once, from $|a|$ to $|a|-1$. In each case the second transition advances the input head once more, so the total input position is $|pre|+3$ (`moveInputPos_pos_of_ne_right`). Unpacking the two buffer blocks and the action application verifies that the untouched second buffer and output remain empty; the first block is identified by `tapeBlocks_left`.

**Key facts.** `Turing.FinTM.a2_map_first`, `Turing.FinTM.a2_mapCfg_read`, `Turing.FinTM.bufferTape_append`, `Turing.moveInputPos_pos_of_ne_right`, `Turing.FinTM.tapeBlocks_left`.
