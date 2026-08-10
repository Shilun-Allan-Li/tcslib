<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean :: Circuit.reidx_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Re-indexing a circuit preserves its depth

**Claim.** For a circuit `c : Circuit m` and any map `f : Fin m → Fin m'`,
`(Circuit.reidx c f).depth = c.depth`. Here `Circuit.reidx` rewrites every leaf
literal `⟨i, s⟩` to `⟨f i, s⟩` and recurses through `node isAnd cs` by mapping
over the children; no hypothesis on `f` is needed (it need not be injective),
because `reidx` changes only leaf indices and leaves the tree shape alone.

**Proof.** Induction with the custom nested-inductive principle
`Circuit.ind`, which supplies `∀ c ∈ cs, motive c` in the `node` case.

1. Literal case: both sides are `0` — `simp [Circuit.reidx, Circuit.depth]`.
2. Node case: `Circuit.depth (.node _ cs) = 1 + cs.foldr (fun c acc => max c.depth acc) 0`,
   and `simp only [Circuit.reidx, Circuit.depth, List.foldr_map]` pushes the
   `List.map` inside the fold, so `congr 1` leaves only the two folds to match.
3. That fold equality is a second, plain `induction cs`: `nil` is `rfl`; in the
   `cons hd tl` case `rw [ih hd List.mem_cons_self]` fixes the head summand and
   `congr 1` plus `ihtl (fun c hc => ih c (List.mem_cons_of_mem _ hc))` handles
   the tail, re-deriving the inner induction hypothesis by weakening membership.

Note the double induction: the outer one is structural on the circuit, the inner
one on the child list, and only the inner one needs the membership-weakening
step.

**Used in.** Nothing in the repository currently cites it; it is the depth half
of the `reidx` interface, kept alongside `Circuit.reidx_eval` (which *is* used,
in `LMN/GateMerge.lean`) so that re-indexing can be applied without disturbing
depth-based size bounds.
