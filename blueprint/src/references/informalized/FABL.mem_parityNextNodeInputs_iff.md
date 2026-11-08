<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.mem_parityNextNodeInputs_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Next-Node Input Membership

**Claim.** An index belongs to the next-node input set precisely when its canonical pair indexing has a position $j$ whose child index is associated to $(g,j)$ and whose sign product differs from $a(j)$.

**Proof.** The next-node input set is defined by filtering the layer indices according to the stated existential condition. Thus an index belongs to it exactly when its canonical pair has first component equal to the child index associated to some $j$ and the product of its signs is unequal to $a(j)$.
