<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: listAnd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Pointwise AND of a list of Boolean functions

**Definition.** `listAnd : List ((Fin n → Bool) → Bool) → (Fin n → Bool) → Bool`
is the pointwise conjunction of a list of Boolean functions, defined by recursion
on the list:

- `listAnd [] x = true` (empty conjunction),
- `listAnd (f :: fs) x = f x && listAnd fs x`.

So `listAnd fs x = true` exactly when `f x = true` for every `f` in `fs`.

**Remark.** This is the top AND gate of a depth-3 AND-of-OR-of-AND circuit
presented as data: the `s₂` second-layer DNF gates are collected with
`List.ofFn (fun i => restrictFn (gates i).eval ρ)` and combined by `listAnd`.
Using a list rather than `∀ i : Fin s₂, …` is what lets the compression step
manipulate the gates structurally (concatenating their CNFs) by list induction.

**Used in.** The conclusion of `depth3_compression`, and its distribution law
`restrictFn_listAnd`.
