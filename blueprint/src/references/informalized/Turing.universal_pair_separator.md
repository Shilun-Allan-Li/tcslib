<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universal_pair_separator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Separator Positions

**Claim.** The paired encoding has $0$ at position $2|\alpha|$ and $1$ at position $2|\alpha|+1$.

**Proof.** Induct on $\alpha$. When $\alpha$ is empty, the encoding begins with the separator $01$, giving the two claimed entries. When $\alpha=b::\alpha'$, the doubled first bit contributes two entries before the rest of the encoding. Thus the positions for the separator shift by two, exactly matching the increase from $2|\alpha'|$ to $2|\alpha|$. The induction hypothesis gives $0$ and then $1$ at those shifted positions.
