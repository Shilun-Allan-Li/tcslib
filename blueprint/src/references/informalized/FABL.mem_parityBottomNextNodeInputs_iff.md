<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.mem_parityBottomNextNodeInputs_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bottom Next-Node Input Membership

**Claim.** An index belongs to the bottom next-node input set precisely when its canonical pair indexing has a position $j$ whose child index is associated to $(g,j)$ and whose normalized sign product differs from $a(j)$.

**Proof.** By definition, the bottom next-node input set consists of those layer indices satisfying the displayed existential condition on their canonical pair: there must be a position $j$ with first component equal to the child index associated to $(g,j)$ and normalized sign product unequal to $a(j)$. Membership in a filtered finite set is exactly satisfaction of its filter predicate, which gives the equivalence.
