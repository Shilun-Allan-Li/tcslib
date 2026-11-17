<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPThreeQuery.lean :: FABL.liftLocalClause_width -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width preservation under lifting

**Claim.** Lifting a clause from $r+a$ coordinates to $r+K$ coordinates preserves its width.

**Proof.** The lifted clause is formed by applying the literal-lifting operation to every literal in the original list. This changes each literal's index but leaves the list's length unchanged. Since width is the number of literals, the two widths are equal.
