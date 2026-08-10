<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitTreeManip.lean :: list_child_signed_dnfs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Signed DNFs for a whole list of depth-≤-1 children

**Claim.** Let `cs : List (Circuit m)` have every member of depth `≤ 1`, and let
each gate function `gates i` have a width-`≤ l` DNF and a width-`≤ l` CNF
representation. Then there are families `φs : Fin cs.length → DNF n` and
`signs : Fin cs.length → Bool` such that each `φs j` has width `≤ l`, every term
of `φs j` is variable-injective and `Nodup`, and for all `j, x`

`(if signs j then (φs j).eval x else !((φs j).eval x)) = (cs.get j).eval (fun i => gates i x)`.

**Proof.** Pointwise choice, nothing more.

1. `have h_choose : ∀ j : Fin cs.length, ∃ φ sign, …` — for a fixed index this is
   exactly `child_depth_le1_has_signed_dnf` applied to `cs.get j`
   (`apply_rules`), whose depth side-goal `(cs.get j).depth ≤ 1` follows from
   `h_depth` by `grind` (membership of `cs.get j` in `cs`).
2. `choose φ sign hφ hsign using h_choose` turns the family of existentials into
   functions of `j`.
3. Repackage: the conclusion's four conjuncts are `hφ`, `hsign j |>.2.1`,
   `hsign j |>.2.2`, and `hsign j |>.1 x`.

**Remark.** A granular plumbing helper: it only converts "for each index there
exists a signed DNF" into "there exist index-parameterised families", which is
the form the depth-2 collapse needs to build a literal circuit whose `j`-th
literal carries `signs j`.

**Used in.** `exists_circuit_depth_reduction_depth2`.
