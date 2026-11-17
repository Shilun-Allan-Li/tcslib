<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.bribeFunction_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bribing an Enlarged Coordinate Set

**Claim.** Bribing the coordinates in $J\cup\{i\}$ to $b$ agrees with first setting coordinate $i$ to $b$ and then bribing the coordinates in $J$ to $b$.

**Proof.** Compare the resulting inputs coordinate by coordinate. The identity that bribing an inserted coordinate set has this effect (`bribeInput_insert`) says precisely that replacing coordinates in $J\cup\{i\}$ by $b$ gives the same vector as setting coordinate $i$ first and then replacing the coordinates in $J$. Applying $f$ to these equal inputs gives equal outputs at every input, hence the claimed equality of functions.

**Key facts.** `FABL.bribeInput_insert`.
