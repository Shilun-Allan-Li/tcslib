<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTail_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One write-sweep cell update

**Claim.** Updating the induced binary tape at position $(N+1)p+j$ to the $j$th entry of $E(w)$ turns the counter-$(j+1)$ family into the counter-$j$ family.

**Proof.** It suffices to compare the two tapes at every block coordinate $(N+1)z+b$. The block-coordinate reading rule (`arTape_at`) identifies the tape value there with the corresponding entry of its block, while the coordinate equality criterion (`arPos_eq`) identifies when this position is the updated position: precisely when $z=p$ and $b=j$. If $z\ne p$, neither family changes that block entry. If $z=p$ and $b=j$, the pointwise update supplies $E(w)_j$, exactly the entry selected by the counter-$j$ family. If $z=p$ but $b\ne j$, the update leaves the entry alone; the threshold conditions at counters $j+1$ and $j$ agree for this offset, since an integer offset distinct from $j$ cannot lie between those consecutive thresholds. Hence the tapes agree at all block coordinates, and extensionality along those coordinates (`arTape_ext`) gives equality.

**Key facts.** `Turing.FinTM.arTape_at`, `Turing.FinTM.arPos_eq`, `Turing.FinTM.arTape_ext`.
