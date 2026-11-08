<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean :: Turing.vhostSilent_layout -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent-Simulation Tape Layout

**Claim.** Among the $m+2$ tape indices, an index lies in the embedded first $m+1$ tapes exactly when it is less than $m+1$; the only index outside that image is the final index.

**Proof.** An index in the image of the standard embedding has the form obtained from some index below $m+1$, so its value is below $m+1$. Conversely, any index whose value is below $m+1$ gives an index in the source finite set, and the embedding maps it to the given index. Thus image membership is equivalent to having value below $m+1$. Since every index in the larger finite set has value at most $m+1$, failure of that strict inequality means its value is exactly $m+1$, which is precisely the final index. This proves both characterizations.
