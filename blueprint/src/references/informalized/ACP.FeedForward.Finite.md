<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/FeedForwardCircuit.lean :: Finite -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Layerwise finiteness of a circuit

**Definition.** For `F : FeedForward α inp out`, the proposition `F.Finite` says that
every layer is a finite type: `∀ i, Finite (F.nodes i)`. It is a `protected abbrev`, so
it is reducible and `protected` only to avoid clashing with Mathlib's `Finite`.

**Remark.** This is a one-line abbreviation, not a lemma. It names the hypothesis under
which `F.size` (a `Nat.card` of a sigma type) is meaningful rather than `0`.

**Status.** Currently unused: no other declaration in `TCSlib` mentions
`FeedForward.Finite`. The Razborov–Smolensky files instead write the assumption in
unfolded form as an instance binder `[∀ i, Finite (F.nodes i)]` and upgrade it to
`Fintype` with `Fintype.ofFinite`, so the abbreviation is dead code as it stands.
