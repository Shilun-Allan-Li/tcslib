<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_symbol_ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean symbols determined by indicators

**Claim.** If $u,v\in\{\mathrm{none},\mathrm{some\ false},\mathrm{some\ true}\}$ agree on whether they equal $\mathrm{some\ false}$ and agree on whether they equal $\mathrm{some\ true}$, then $u=v$.

**Proof.** The proof checks the three possible forms of each option. If either is `none`, agreement of the two indicators rules out the other being `some false` or `some true`, so both are `none`. If both are present, each Boolean value is either false or true; the indicators distinguish these two possibilities, and their agreement forces the values to match. In every case the options are equal.
