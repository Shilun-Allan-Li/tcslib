<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityTreeValue_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base case for parity trees

**Claim.** At depth zero, the parity tree value at index $g$ is the padded input: it equals $x_g$ when $g<n$ and $1$ otherwise.

**Proof.** This is the defining depth-zero clause of the parity tree, which assigns the value of the padded input at index $g$. By definition, that input is $x_g$ when $g<n$ and is $1$ when $g\ge n$.
