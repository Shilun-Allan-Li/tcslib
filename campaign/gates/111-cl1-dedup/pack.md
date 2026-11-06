# External audit pack: dedup CL-1, the codec languages' shared lemma and decider wrapper (PR #220, a dedup gate)

## Why this PR

**CL-1** (`campaign/duplication-ledger.md`) concerns the five code languages of
`SpaceComplexity/Codec`: `validLang`, `initLang`, `acceptLang`, `stepLang` and `edgeLang`. Each
had its own membership lemma, its own `_iff` through the word-level check, and its own decider.
Two pieces were repeated across them:
- the decoding of `⟨x, ⟨bits c, bits s⟩⟩` (`pairEncode_inj` twice, then `bits_injective`);
- the decider wrapper (`arm_decides_poly` on `CA`, the `one_run` split, the indicator rewrite and
  the reject branch).

At gate 91 they formed 31 copy pairs, plus 25 more with `edgeLang`.

The user accepted CL-1 as debt on 2026-11-04. On 2026-11-06, with the owner (Hydroxyi) inactive,
the user ruled the **full refactor**:
- **Q1:** add `mem_validLang_iff`, `mem_initLang_iff`, `mem_acceptLang_iff` and
  `mem_stepLang_iff` (`Iff.rfl`) beside the existing `mem_edgeLang_iff`, so that rule 10 holds
  without unfolding;
- **Q2:** one shared lemma with a generic injective tail; `stepLang_mem` stays outside the
  wrapper, because its run goes through `parse_run₂` with no `one_run` split.

**The PR:** #220 on `lean/dedup-cl1`, head `c4aa5dc0` (full hash in the bundle header). It
consists of `2e9ec6fc` (the shared lemma and characterizations; `Langs`, `Checks`), `533af323`
(the wrapper; `Deciders`), and merges of the campaign. It changes 3 files: 209 lines added, 175
removed (`evidence/landing/cl1.diff`).

## What changed (verify)

**New public declarations:**
- In `Langs`:
  - the four `mem_X_iff`, each `Iff.rfl` with a docstring stating the formula;
  - ```lean
    theorem mem_codeLang_iff {τ : Type} {enc : τ → List Bool} (henc : Function.Injective enc)
        {L : Language Bool} {P : List Bool → ℕ → τ → Prop}
        (hL : ∀ y, y ∈ L ↔ ∃ (x : List Bool) (c : ℕ) (t : τ),
          y = pairEncode x (pairEncode (Nat.bits c) (enc t)) ∧ P x c t)
        (x w : List Bool) (t : τ) :
        pairEncode x (pairEncode w (enc t)) ∈ L ↔ ∃ c, Nat.bits c = w ∧ P x c t
    ```
    The tail is `bits s` for the four triple languages and `⟨w', bits s⟩` for `stepLang`.
- In `Deciders`: `oneCode_mem (hm : mode ≠ .step) … : L ∈ LOGSPACE`. Its hypotheses are:
  - `hL`: the triple characterization;
  - `hP`: the predicate makes `c` a configuration code;
  - `hchk`: the word-level `_iff`;
  - `hval`: the check implies `ValidChk`;
  - `htail`: the mode's tail answers `b` with `Chk x s w ↔ b = true` from `one_run`'s registers.

**Re-proved through them (14 members, statements unchanged):**
- the five `mem_X` (`Langs`);
- the five `X_iff` (`Checks`);
- the four deciders `validLang_mem`, `acceptLang_mem`, `initLang_mem` and `edgeLang_mem`
  (`Deciders`). These keep their own tail and check-to-verdict conversion. Their reject branches
  now read the language through `mem_X_iff`.

**Not changed:**
- `stepLang_mem`, as ruled;
- the shape-uniqueness decodes (`Shape1`/`Shape2`), which decode word against word;
- the `Parse` sites;
- `TQBFHardMachine`'s two decodes, which are outside CL-1. They are recorded in the scope as later
  candidates (`campaign/items/dedup/cl1-SCOPE.md`).

`cfgWord_eq_bits_iff` (`Checks`) is kept, though now unused: it is public and not a copy.

## Known deviations (for the audit)

- **Pre-existing rule-10 reads not in CL-1:** the deciders still unfold `AcceptChk`, `InitChk`
  and `CA`, as at the base (`simp [PreS, CA]`, `rw [AcceptChk]`, `rw [InitChk]`). The read
  `hval := h.1` moved from the old reject branches. `CA` is ledger family MT-1's kind (machine
  tables). The check predicates are to be recorded with it.
- **A small sibling pair within the family:** each step proof needs the three-line reshuffle of
  `stepLang`'s `∃ x c c' s` into the generic tail (`mem_stepLang` with `ℕ × ℕ`, `stepLang_iff`
  with `List Bool × ℕ`).

## Brief for the auditor

1. **The shared lemma and the wrapper:** are they correctly stated and general enough? Do all 14
   members now go through them? Is anything left repeating the decoding or the wrapper skeleton?
2. **Rule 10:** do `Checks` and `Deciders` read the five languages only through the published
   `mem_X_iff`? The seal is below.
3. **Scope:** are the exclusions right (`stepLang_mem`, the shape decodes, `Parse`)?
4. **Public text:** are docstrings, attributions and sketches in place? The files are a
   colleague's.

## Repository-side attestations (verify or challenge)

- **Freeze** (`evidence/freeze/`, the head against the campaign `e4e7a419`):
  - `Langs`: 12 → 17 public (the four `mem_X_iff` and `mem_codeLang_iff`), with the five `mem_X`
    bodies changed;
  - `Checks`: 31 → 31, with the five `X_iff` bodies changed;
  - `Deciders`: 20 → 21 (`oneCode_mem`), with the four `X_mem` bodies changed.

  No statement changes, and no private declarations added, removed or changed.
- **Rule 10** (`evidence/seal/`): copies of `Checks` and `Deciders` with
  `attribute [local irreducible]` on the five languages. They are elaborated against an overlay in
  which the PR's `Langs` and `Checks` are compiled (`compile-*.out`, exit 0).
  - The controls: an unsealed destructuring of a `validLang` membership succeeds, and the same
    destructuring fails under the seal for each of the five languages (`fail_if_success`).
  - **Both copies give exit 0 and 0 errors.** The only warnings are the controls' unused
    variables.
- **Screen** (`evidence/screen/`, all `Codec` files): the base has 183 declarations, 82 pairs
  and 28,119 characters; the head has 185, 59 and 17,519. **0 new pairs, 23 gone** (the family's
  copies: `mem_stepLang` against the other `mem_X` at 94%, the deciders against each other at
  67–79%, …; `pairdiff.txt`).
- **Lint** (`evidence/lint/`):
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 81 WARN over 112 files at base and head.
  - The policy linter gives 0 findings on the 3 files at both.
- **Replay** (`evidence/merged-tree/`): `replay-lcl2` at `c4aa5dc0` covers the downstream closure
  of the 3 files (60 modules), chained from the campaign snapshot after #216. **60 modules, 0
  failed.** The static check finds 0 mismatches. The 21 `sorry` warnings are `ClassPSPACE/TQBF`'s
  existing ones. #217, #211, #218 and #219 merged afterwards. None of the 3 files imports a module
  they changed in a way that matters, and #220 changes only proof bodies and adds lemmas.
  `Randomized/SpaceAmplifyPolyCode` and `SpaceAmplifyPolyRun` define same-named
  `Randomized.PolyAmp.mem_initLang_iff`/`…acceptLang_iff`/`…stepLang_iff` while opening
  `Complexity.Codec`. Both are in the replay and resolve to their own lemmas.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/111-cl1-dedup/findings.md`. The gate closes when it has zero blockers and zero
majors.

**Deliver your findings as a downloadable Markdown file named `cl1-dedup-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
