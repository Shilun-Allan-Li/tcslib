# Wee20.Linear.scheme_raw_correct assembly proof draft

Status: exact-header replacement, checked by inspection only. No live files edited;
no Lean, lake, build, or Git commands. Native elaboration remains with the parent.

## Deliverable

`LinearSchemeRawCorrect.lean.inc` replaces only the existing admitted body of
`scheme_raw_correct`, currently `Wee20/LinearCorrect.lean:156`. A Python textual
assertion matched its entire existing header through `:=`. The draft contains one
tactic block, no helper declarations or new admitted terms, and maximum line width
90 columns. No new imports are needed.

The proof is exactly:

```lean
  simpa only [scheme_raw_eq] using (pi_dec_eq G PG zDim κ pp f M x z a s t)
```

The published bundle equality exposes the four explicit cores; ordinary let/record
projection reduction aligns the bundled statement with the existing core-correctness
statement. No algorithm definition or generated defining equation is explicitly unfolded.

## Explicit remaining dependency

This is proof assembly only. It retains the existing `pi_dec_eq` theorem dependency.
At inspection time `pi_dec_eq` is still admitted in the live file, so this draft does
not establish an admission-free correctness chain or eliminate its `sorryAx` dependency.
That substantive proof remains to be completed separately. The exact argument order
used is `G PG zDim κ pp f M x z a s t`.

Other dependency: `Wee20/Linear.lean:391`, the published `scheme_raw_eq` reader:

`scheme_raw G PG zDim κ pp =
  ⟨setupCore G ℓ zDim κ pp, encCore G ℓ zDim κ pp,
    keyCore G PG zDim κ pp, dec G PG zDim κ pp⟩`.

The source theorem at `LinearCorrect.lean:140` has precisely the resulting expression.
No helper, sampler, efficiency assumption, group-exponent witness, or statement change
is introduced. No false or unattainable claim was found.

## Actual search/read record

Working tree:
`/Users/seyoonr/.codex/worktrees/tcslib-io-phfe/tcslib-exchange`.

```sh
rg -n -A 32 -B 8 'theorem scheme_raw_correct|theorem pi_dec_eq' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/LinearCorrect.lean
rg -n -A 36 -B 15 'theorem scheme_raw_eq|def scheme_raw|structure RawAlgorithms' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/Linear.lean
rg -n 'scheme_raw_eq|scheme_raw_correct' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption
rg -n 'dsimp only.*_eq|simp only \[.*raw_eq|rw \[.*raw_eq' TCSlib/Cryptography/AdvancedEncryption/FunctionalEncryption/Wee20/*Correct*.lean
```

The first three searches confirmed the exact law/reader match. The final search for
existing assembly-proof patterns found no matches; no new helper was considered necessary.
Textual checks verified header equality, width, one tactic block, and no admitted terms.
These are preparation checks, not native Lean validation.
