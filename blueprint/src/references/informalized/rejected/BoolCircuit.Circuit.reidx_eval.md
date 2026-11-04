<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitReindex.lean :: Circuit.reidx_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Re-indexing commutes with evaluation

**Claim.** For `c : Circuit m`, `f : Fin m → Fin m'` and an assignment
`g : Fin m' → Bool`, `(Circuit.reidx c f).eval g = c.eval (g ∘ f)`. That is,
relabelling the input variables of a circuit is the same as pre-composing the
assignment with the relabelling — again with no hypothesis on `f`.

**Proof.** Induction via `Circuit.ind`.

1. Literal case: `Lit.eval ⟨f l.idx, l.sign⟩ g` and `Lit.eval l (g ∘ f)` both
   reduce to `if l.sign then g (f l.idx) else !g (f l.idx)` —
   `simp [Circuit.reidx, Circuit.eval, Lit.eval, Function.comp]`.
2. Node case: after `simp only [Circuit.reidx]`, `cases isAnd` splits the AND
   fold (`&&`, unit `true`) from the OR fold (`||`, unit `false`); both branches
   are discharged by the *same* script, applied with `<;> ·`, since
   `simp only [Circuit.eval, List.foldr_map]` turns each into a fold over the
   mapped child list.
3. In both branches an inner `induction cs` closes the fold equality: `nil` is
   `rfl`; `cons hd tl` uses `rw [ih hd List.mem_cons_self]` for the head and
   `ihtl (fun c hc => ih c (List.mem_cons_of_mem _ hc))` for the tail.

**Used in.** `LMN/GateMerge.lean` (two call sites), where a merged gate is built
by re-indexing children and the evaluation must be shown unchanged; there the
lemma is followed by `congr 1; ext i; simp` to identify `g ∘ f` with the
intended assignment.
