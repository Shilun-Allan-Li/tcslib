<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTape_update -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating an induced tape

**Claim.** Updating the induced tape at $(N+1)z+j$ gives the tape induced by changing only entry $j$ of block $z$ to $b$.

**Proof.** Compare the tapes at an arbitrary block coordinate $(N+1)z'+j'$. The block-coordinate reading rule (`arTape_at`) identifies the original induced tape there with $F(z',j')$. The coordinate equality criterion (`arPos_eq`) says this position is the update location exactly when $z'=z$ and $j'=j$. Consequently the updated tape has value $b$ at that coordinate and retains $F(z',j')$ elsewhere, exactly as in the stated block family. Extensionality along block coordinates (`arTape_ext`) then gives equality of the tapes.

**Key facts.** `Turing.FinTM.arTape_ext`, `Turing.FinTM.arTape_at`, `Turing.FinTM.arPos_eq`.
