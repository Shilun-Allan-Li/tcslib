<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_sparse_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clearing the Next Captured Cell

**Claim.** For a natural number $p$, a Boolean value $b$, and a finite Boolean list $r$, blanking cell $p$ of the sparse tape encoded by $p$ blank entries followed by $b$ and $r$ yields the sparse tape encoded by $p+1$ blank entries followed by $r$.

**Proof.** Compare the two tapes at each integer position $z$. At $z=p$, the update explicitly makes the cell blank, and the new encoding also has a blank there. If $z<0$, both tapes are blank by the definition of the sparse tape. It remains to consider nonnegative $z\ne p$. The update then leaves the original tape unchanged. For $z<p$, both encodings read one of their initial blank entries. For $z>p$, the original list reads the corresponding entry of $r$ after passing the first $p$ blanks and the cell containing $b$; the new list reads that same entry after passing $p+1$ blanks. Thus the tapes agree at every integer position.
