<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.joinFields_cons_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Joining the First Two Fields

**Claim.** Joining the fields in $u::v::fs$ yields $u$ mapped to optional elements, followed by a blank separator and the joined fields in $v::fs$.

**Proof.** Joining fields inserts the singleton blank list between consecutive fields after mapping each field element to its optional form. For the first two fields, this gives the mapped list from $u$, then the separator `none`, then the intercalation of the remaining fields $v::fs$. This is the stated list identity.
