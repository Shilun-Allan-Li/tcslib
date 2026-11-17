<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/EmitIterBody.lean :: Turing.embed_ofWords_left -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedding a Word Configuration

**Claim.** If $E$ has at least one work tape, then embedding the configuration with state $q$ and word $s$ on tape $0$ into $\max(k_E,k_G)$ tapes gives the configuration with the corresponding left-call state and $s$ on tape $0$.

**Proof.** The word-configuration embedding formula identifies the embedded configuration with one whose tape $i$ contains the original word on tape $i$ when $i<k_E$, and is empty otherwise (\texttt{embedCfg\_ofWords}). The state is mapped to the corresponding left-call state, while the input-head position, work-head positions, and output are those of the word configuration. It remains to compare the tape words with the target configuration. For any $i<k_E$, the word is $s$ exactly when $i=0$ and is empty otherwise. If $i\not<k_E$, the assumption $k_E>0$ ensures $i\ne0$, so both the embedded tape and the target tape are empty. Thus the tape contents agree at every index, proving the configuration equality.

**Key facts.** `Turing.embedCfg_ofWords`.
