# New-body argument inspection

- `apply sph_linear_ne_NP_of_padding space_hierarchy`: same-home frozen helper and public theorem; no foreign definition is opened.
- `mem_SPACE_padLang`: public proved padding transfer, at coefficient 1, degree 2 and T m = m + 1.
- `Nat.pow_le_pow_left (Nat.le_succ n) 2`: public Mathlib inequality; no copied bound proof.
- `dsimp only`: an empty explicit argument list, reducing the local T lambda/arithmetic; no foreign TCSlib definition is named.
- `omega`: arithmetic at the instantiated input length; no TCSlib unfolding argument.
- `Set.ext`: core/Mathlib extensionality; `mem_padLang_iff` is the published reading of the foreign padLang definition.
- `rwa [he]`: the only explicit rewrite argument is the freshly proved local language equality `he`.
- No `simp [Def]`, `unfold`, `show`, `change`, `Nat.find`, manual buffer indexing, machine construction or configuration-extensionality block was introduced.

The new-region seal covers SPACE, NP, padLang and pairEncode, the complete direct foreign-definition inventory of the target and its one generated auxiliary. It removes the four TCSlib definition unfoldings present in the global default simp set. There are no inventory exclusions. The scope is the new target section; this is not a seal of unchanged legacy Hierarchy proofs.
