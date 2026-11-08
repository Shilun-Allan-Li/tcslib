<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.mem_dropWhile_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership after dropping initial smaller elements

**Claim.** For a pairwise strictly increasing list $l$, an element $c$ belongs to the list obtained by dropping the initial entries less than $a$ exactly when $c$ belongs to $l$ and $a\le c$.

**Proof.** Induct on the list. The empty list satisfies both sides vacuously. For a list beginning with $x$ and tail $xs$, there are two cases. If $x<a$, the first entry is dropped, and strict increase ensures that every later entry is greater than $x$. The induction hypothesis applied to the tail then says that its retained entries are exactly those belonging to the tail and at least $a$. If $x\not<a$, linear ordering gives $a\le x$; no initial entry is dropped, and strict increase puts every later entry above $x$, hence also at least $a$. Thus the retained list contains exactly the entries of the original list that are at least $a$, proving the equivalence.
