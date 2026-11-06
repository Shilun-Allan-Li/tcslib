# Gate 03a, round 3: external delta-audit findings

**Verdict: CLOSE — 0 blockers, 0 majors, 0 minors; 1 scope note.**

All five round-2 findings are resolved. This verdict covers the specified documentation repairs and records at `3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e`, with #205's Lean head `0cebd6aad24ad0c79a3b2917bfa9f8158c59af75`. It does not certify unrelated declarations or discharge the separately scheduled duplication cleanup.

I followed `03a-pack-r3.md`, read the prior findings, resolutions, repair diff and affected definitions, and checked the attached source at book pp. 23–24, 27–28 and 69–73 (PDF pp. 35–36, 39–40 and 81–85). I also inspected rendered book pp. 24 and 69. This is a documentation and statement-delta audit; I did not run Lean or audit tactic proofs.

## Findings

Paths beginning with `Complexity/` or `Cryptography/` are relative to `TCSlib/`. Line numbers refer to the bundled current files.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-N1 | note | `03a-pack-r3.md`; `evidence-repairs/03a-r2/repair.diff.txt` | The supplied diff accounts for the round-3 Lean repair. | It exactly matches #205: **five comment blocks**, comprising the module comment and four declaration docstrings, across three files. The broader round-2-to-round-3 comparison additionally contains #204's two `OneWay.lean` docstring corrections (`WorstCaseOneWayLit` and `ofString`). No other Lean file changes, and all four files retain identical non-comment contents. | No Lean repair required. For precise bookkeeping, replace “four docstrings” with “five comment blocks” and understand “whole Lean change” as the #205 repair, with #204 retained as the separately disclosed context. |

## Round-2 resolutions

- **R2-1: fixed** — `PPT.lean:44–50` and `:246–250` explicitly restrict the efficient-computation claim to `advInput n y = ⟨1^n,y⟩`, allow arbitrary values off that domain, and give the actual normalized converse. DESIGN D3 (`DESIGN.md:63–68`) now qualifies the source attribution by the same domain restriction. Read with these explicit qualifications, the earlier shorthand references to Definition 24.6 do not assert full-domain computability. DESIGN does not repeat the converse formula; both repaired Lean comments do, and it matches the pinned theorem.
- **R2-2: fixed** — `Adversary.lean:103–108` now requires a nonconstant `PolyExpr` output length in its parenthetical. The `ofString` example (`OneWay.lean:196–212`) uses `p = var` and an ordinary branch whose nonempty outputs end in `1`; its padded special outputs end in `0`. This removes the padding collision from round 2. The example remains explicitly informal and conditional on a length-preserving one-way function.
- **R2-3: fixed** — `Ensembles.lean:119–124` states only the necessary dyadic-law condition, explicitly rejects its converse, and specifies distinct outputs for the three-seed example. The erratum at `review/gate03a-review.md:66` correctly distinguishes a constant map from `Fin 3` from a law having an atom of mass `1/3`.
- **R2-4: fixed** — DL-9 (`duplication-ledger.md:36`) now names the private `Ensemble.blocks`, its file, and the re-pointing of `Ensembles.lean`. I also checked the pinned cleanup-part-2 draft: item A expressly schedules deletion of this copy and re-pointing of its users. The accounting is repaired; the actual duplicate remains scheduled debt.
- **R2-5: fixed** — `Ensembles.lean:188–195` now says padding “can be lossy otherwise” and marks exact target length as sufficient. This permits injective padding on shorter supports while retaining the valid collision warning.

## Mathematical checks of the repairs

**Restricted computation.** The definition still says exactly

\[
 A.\mathrm{Computes}\,f
 \iff \forall n,y,r,\quad
 A.\mathrm{runAt}(n,y,r)=f(\mathrm{advInput}(n,y)).
\]

For uniform `A`, the unchanged `Computes.polyTimeComputable` concludes

\[
 \operatorname{PolyTimeComputable}
 \bigl(z\mapsto f(\mathrm{advInput}(|\mathrm{pairFstD}(z)|,
                                      \mathrm{pairSndD}(z)))\bigr).
\]

On an input `z = advInput n y`, the pair-projection equations make the normalized argument equal to `z`. On other inputs the theorem evaluates `f` at the normalized argument, not at `z`. Thus the round-2 counterexample with uncomputable off-domain values remains possible and is now accurately disclosed. Definition 24.6 instead requires correctness on every input string. Zero coins cause no vacuity: their space has one element.

**Inversion.** The constructors of `PolyExpr` give polynomials with natural-number coefficients. A nonconstant evaluated polynomial has a positive coefficient in some positive degree, so for natural numbers `a < b`, that term strictly increases and every other term is nondecreasing. Its evaluation is therefore injective, including at zero. Here “nonconstant” means the evaluated length function, not merely a syntactic occurrence of `var`.

For the corrected example, use the docstring's `f`, `g` and `h`, and consider positive input length `n`. At even length `n = 2k`, the special inputs are `0^k ‖ w` with `|w| = k`; their uniform probability is

\[
 \frac{2^k}{2^{2k}}=2^{-k}=2^{-n/2}.
\]

At odd length there are no special inputs. On an ordinary challenge the padded family output is `g(x)`, ending in `1`. A same-length special preimage produces an output ending in `0`, so it cannot succeed. Every successful typed answer on an ordinary challenge consequently inverts `g`. Coupling the input and inverter coins in the two experiments gives

\[
 \Pr[\text{typed inversion succeeds}]
 \le \Pr[\text{the same inverter inverts }g]
       +\begin{cases}2^{-n/2}&n\text{ even},\\0&n\text{ odd}.\end{cases}
\]

This verifies the stated asymptotic bound. Inverting `g(x ‖ b)=h(x) ‖ 1` yields a preimage of `h` by dropping the answer's last bit; the length shift is one. Conversely, the raw unrestricted experiment is inverted by `y ↦ 0^{|y|} ‖ y`. For the empty input, complete the length-preserving `g` by `g([])=[]`; the same inverter then also succeeds there. No existence or Lean formalization of the assumed one-way function is asserted.

**Sampling and padding.** An exact sampler using finitely many uniform bits assigns every event an integer divided by a power of two. This excludes an atom of mass `1/3`, but not a constant `Fin 3` sampler, which is a point mass. A point mass at an uncomputable parameter-dependent bit cannot have an efficient exact sampler: every coin string has positive probability, so evaluating that sampler on all-zero coins would compute the bit. These checks justify both directions of the repaired warning. Finally, padding `[false]` and `[true]` to two bits preserves their distinction, whereas padding `[true]` and `[true,false]` to two bits identifies them. Exact target length is sufficient for faithful representation, not necessary for injectivity on a particular support.

## Change and evidence verification

- The three-file supplied diff exactly matches the patches returned for [#205's head commit](https://github.com/Shilun-Allan-Li/tcslib/commit/0cebd6aad24ad0c79a3b2917bfa9f8158c59af75). Reverse application succeeds; all old and new Git-blob hashes match the diff's prefixes. Comparing all comment blocks finds only the five listed changes. Removing comments leaves **byte-identical contents**, including definitions, statements, proofs, imports and attributes.
- The [head-to-pin comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/0cebd6aad24ad0c79a3b2917bfa9f8158c59af75...3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e) contains no Lean changes. The [round-2-to-pin comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/e28773ef3bda6f7b4b112ec1657427bfef01e374...3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e) has exactly the four Lean files described in R3-N1. I separately reverse-checked #204's recorded patch: `OneWay.lean` also has identical non-comment contents.
- The four bundled Lean snapshots and the three audited records match their full Git-blob hashes at the pin. Supplemental pinned reads were limited to the [normalized converse](https://github.com/Shilun-Allan-Li/tcslib/blob/3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e/TCSlib/Complexity/Randomized/Closure.lean#L417), [polynomial constructors](https://github.com/Shilun-Allan-Li/tcslib/blob/3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e/TCSlib/Complexity/Randomized/PolyExpr.lean#L73), [#204 repair diff](https://github.com/Shilun-Allan-Li/tcslib/blob/3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e/briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03b-r2/repair.diff.txt), and [DL-9 cleanup scope](https://github.com/Shilun-Allan-Li/tcslib/blob/3f40dfbc32481ebf28b6eb485f7593fa30bf4d1e/briefs/pass-shelat-ch5-8/fills/cleanup-part2/brief-draft.md#L17).
- The supplied replay has **80 distinct module entries**, all `rc=0` and `errors=0`, with **63 total `sorry` warnings**. The lint log reports zero findings in each of the three changed files. These are maintainer execution records, not independently reproduced runs. The corresponding pre-repair 63-warning run and `evidence/a2/axioms.log` are not included in this round's bundle; the prior axiom assessment is carried forward, supported by the absence of code changes.
- The bundle has **16 sections**, SHA-256 `71190d2cdc60a5d270f6e899b7ec58084e66221c8a16734079c8479dcef82074`; no independent expected bundle hash was supplied. Removing the separator's one extra trailing newline from the embedded round-2 findings recovers the stated SHA-256 `573714c93cd3f163c75b085b7e7c1ef4ebf35c5ab50fefc7118b48687a064b6b`.

**Notation.** `⟨u,v⟩` is the existing pair encoding; `|u|` is string length; `‖` denotes concatenation; `0^k` denotes `k` false bits. `A` is the machine or inverter under discussion; `f,g,h` are the functions in the audited statements/example; `n,k,a,b` are natural-number parameters or lengths, except the appended `b` in `x ‖ b`, which is a bit; `x,y,z,w,u,v` are strings. Probabilities in the inversion comparison use a uniform length-`n` input and the same inverter's uniform coins. Other identifiers retain their Lean meanings.
