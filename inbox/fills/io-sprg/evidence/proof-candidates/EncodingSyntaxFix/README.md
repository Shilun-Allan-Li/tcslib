# Encoding candidate syntax repair

Untested corrected copies of Encoding6 injectivity and one length candidate.
Only incomplete typed-have syntax is repaired using a placeholder and same-indent swap.
Each proof file retains exactly one outer tactic block. Idx, IdDraw and Seed are unchanged.
No implementation file, statement or import changed. No Lean, Lake, git or cache invoked.

Static API review: pairEncode_injective is Function.Injective on the pair of words;
its implicit a₁/a₂ placeholders match these applications. Modular vector/matrix injection
accepts width then the modulus bound. Nat.lt_two_pow_self has implicit n in Core, so
its existing un-applied usage is correct. natToList_injOn takes the two strict fit
bounds then the word equality. List.ofFn_injective and the two new Basic fixed-width
helpers match the staged applications. The length candidate reduces to a natural
linear combination of the existing three product inequalities; omega success is
unverified. Local function unfolding during fixed-width reader matching remains
an elaboration detail for root's serial compiler check.

Buckets: 1 syntax repair. OneDraw: 2. Draw: 2. Length: 1.
All API searches were read-only against the current worktree/toolchain sources.
