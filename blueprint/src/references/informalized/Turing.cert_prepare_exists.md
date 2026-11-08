<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CertShell.lean :: Turing.cert_prepare_exists -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded Virtual-Host Preparation

**Claim.** There is a finite-state Boolean machine that, from the encoded pair $(x,u)$ on its designated tape, reaches a configuration representing the specified virtual-host setup within a linear bound in $|x|+|u|+1$, without visiting its designated exit state earlier.

**Proof.** Construct the preparatory machine as a sequence of copying, decoding, and simulation stages. First use machines that compute the first and second components of the pair encoding, and install each as a machine call whose exit is a first return. Reserve disjoint blocks of work tapes for the input buffer, the first-component computation, the second-component computation, and the virtual-host tapes; choose a further tape outside the virtual-host block as the capture tape. The indices are distinct by their placement in these blocks.

Copy the encoded pair into the workspace for the first-component computation. Decode its first component, then transfer that result to the virtual-host input buffer. Transfer the original encoded pair to the workspace for the second-component computation, decode its second component, and transfer that result to the virtual-host bank corresponding to tape $j$. At every stage the relevant destination is blank, so the copying and transfer procedures apply. The pair-decoding identity guarantees that these computations recover exactly $x$ and $u$. The embedded-call theorem transports each installed computation to its larger tape block and preserves its first-return property; the sequential-composition theorem joins successive stages while retaining a first-return guarantee for the composite exit.

The stage bounds combine to give the stated bound with coefficient $30+a_f(3f+4)+a_s(3s+4)$, where $a_f,a_s$ and $f,s$ are the installation and computation constants for the two decoders. The pair-encoding length formula bounds the copying and transfer costs, and the decoder call bounds are linear in the encoded length and decoded output length. Finally, the workspace tape assignment is shown to equal the required virtual-host assignment: the buffer tape contains $x$, the bank contains $u$ on tape $j$ and blanks elsewhere, and the capture tape is blank. The virtual-host configuration has the required initial state, input-head position, and empty output, so the silent-embedding word identity identifies the completed configuration with the claimed target. The construction’s first-return guarantees ensure that the exit state was not visited earlier.

**Key facts.** `Turing.FinTM.computesFunInTime_pairFst`, `Turing.exists_installCallTM`, `Turing.cert_call_cut`, `Turing.FinTM.computesFunInTime_pairSnd`, `Turing.cert_bank_word`, `Turing.cert_embed_call`, `Turing.cert_seq`, `Turing.copyTM_run`, `Turing.pairDecode_pairEncode`, `Turing.transferTM_run`, `Turing.length_pairEncode`, `Turing.cert_silent_words`.
