<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecRow_realize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Realization of Codec Rows

**Claim.** Every codec row is the row of some configuration on a Boolean input of length $n$, and that configuration lies in the window of radius $s$.

**Proof.** 1. Set $x$ to be the list whose entries are given by the row’s input function. By construction, $x$ has length $n$. Define a configuration $c$ with the row’s state and input-head position. At each work-tape position $z$, put the row’s symbol at the code for $z$ when $|z|\le s$, and put a blank symbol outside this window. Set each work-tape head position to the integer represented by the row’s head code, shifted by $-s$. Choose the output word to be empty, $[\mathrm{true}]$, or $[\mathrm{false}]$ according as the row summary is empty, accepting, or dead.

2. Every head code represents an integer in the interval $[-s,s]$, so the chosen head positions lie in the window. By the definition of the work tapes, their contents outside the window are blank. Hence $c$ is in the window of radius $s$.

3. The input field of the constructed configuration’s row is the original input function, since the list was formed from that function. For each window coordinate $j$, the corresponding tape position is $j-s$; the position-code identity (\texttt{Complexity.codec_posCode}) says that encoding this position returns exactly $j$. Thus the symbols and head fields are precisely those of the given row. The chosen output words have the prescribed summaries in each of the three cases. The state and input-head fields were copied directly, so all row fields agree, as required.

**Key facts.** `Complexity.codec_posCode`.
