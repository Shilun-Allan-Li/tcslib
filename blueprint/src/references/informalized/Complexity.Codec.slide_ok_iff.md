<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.slide_ok_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sliding Recurrence Check

**Claim.** The sliding Boolean flag is true exactly when every required position in the padded lists satisfies the recurrence defined by $G$.

**Proof.** First rewrite the sequence of input pairs as the list indexed by $i=0,\ldots,|u|+1$ whose entries are $(u.getD(i,e),v.getD(i,e))$. The equal-length hypothesis ensures that the zip contributes the entries inside the lists, while its two appended copies of $(e,e)$ supply the two boundary entries; outside the list, the default value is $e$. The fold calculation for this indexed sequence (`foldl_slStep_range`) says that its final flag is the conjunction of the checks at all indices $i<|u|+2$: the current middle value must equal $G$ applied to the three consecutive values in the shifted first list. The shifted indexed lists agree, at the positions used by these checks, with $e::v$ and $e::e::u$, respectively. Substituting these identifications gives exactly the stated pointwise condition. Thus either direction follows by reading the same family of checks as a conjunction or as a universal statement.

**Key facts.** `Complexity.Codec.foldl_slStep_range`.
