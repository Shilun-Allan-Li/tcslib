# Gate 03a (probabilistic machines, closure, ensembles: the interface): round 2 resolutions

- **Round 2:** findings `findings/gate03a-r2-findings.md`, verbatim, SHA-256
  `573714c93cd3f163c75b085b7e7c1ef4ebf35c5ab50fefc7118b48687a064b6b`; pin
  `e28773ef3bda6f7b4b112ec1657427bfef01e374`; bundle SHA-256 `521e59d8…` (24 sections). Verdict
  **DO NOT CLOSE: 0 blockers, 2 majors, 3 minors**. All are documentation claims; neither major
  is a counterexample to a Lean theorem. The new public interfaces (`exists_compParam`, public
  `polyTimeComputable_stateFind`) are confirmed.
- **Round 1 rows not resolved in round 2:** #1 (R2-1), #7 (R2-3), #15 (R2-2) and #18 (R2-5).
  The others are fixed, recorded or scheduled.
- **Repair:** docstrings only, in `Complexity/Randomized/PPT.lean`,
  `Cryptography/Asymptotic/Adversary.lean` and `Cryptography/Asymptotic/Ensembles.lean` (PR
  below), plus records: DESIGN D3, the 03a review's erratum and ledger DL-9. R2-2's `ofString`
  part was already fixed by #204 (gate 03b round 2, R2-1).

| Finding | Severity | Resolution |
|---|---|---|
| R2-1 | major | **Fixed** (maintainer: true; `Computes` constrains `f` only on `advInput n y`, so the auditor's `f_bad` is computed by a uniform constant machine). The module docstring and `Computes`' docstring in `PPT.lean`, and DESIGN D3, now say that `A.Uniform ∧ A.Computes f` is efficient computation of `f` **on the encodings `⟨1^n, y⟩`**, not on every string. They also say that `Computes` says nothing about `f` off those encodings, and that the converse `Computes.polyTimeComputable` gives polynomial-time computability of `z ↦ f ⟨1^{|fst z|}, snd z⟩`. No statement changes, and no full-domain interface is added (none is needed). |
| R2-2 | major | **Fixed.** The `ofString` example was corrected in #204 for gate 03b round 2's R2-1, the same defect: `p = var`, `g(x ‖ b) := h(x) ‖ 1`, marked informal, with the role of the final `1` stated. `Adversary.lean`'s parenthetical now reads "length-regular `f` whose output length is a non-constant `PolyExpr`, hence injective in the input length". |
| R2-3 | minor | **Fixed.** `Ensemble`'s deviation now says every efficiently samplable ensemble has dyadic laws but not every dyadic one is samplable (the point mass at an uncomputable bit), and gives the non-dyadic example as three seeds mapped to distinct strings. The 03a review's `Fin 3` sentence carries an erratum (records). |
| R2-4 | minor | **Fixed** (records). DL-9 lists the private `Ensemble.blocks` (`Asymptotic/Ensembles.lean`) and its removal and re-pointing; clean-up part 2's brief draft includes it. |
| R2-5 | minor | **Fixed.** `Ensemble.push`'s docstring says the padding "can be lossy otherwise" and that the exact target length is a sufficient condition. |

**Round 3** is a delta audit of the four rewritten docstrings (`PPT.lean`: the module docstring and
`Computes`; `Adversary.lean`; `Ensembles.lean`: `Ensemble` and `Ensemble.push`) and the records
lines.
