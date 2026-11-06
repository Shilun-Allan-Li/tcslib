# External audit pack: the E-PAD statements, `Complexity.mem_SPACE_padLang` (PR #219, a statement gate)

## Why this PR

B6's H fill (#218, gate 109) proved `space_hierarchy` and ended `SPACE_linear_ne_NP`
([AB09, Exercise 3.2]) in the named escalation **E-PAD**. The library has no host for the
padded-language space decider. The user ruled on 2026-11-06:
- E-PAD's API publishes a **general** lemma (any space bound, a polynomial unary pad);
- it goes in a **new `SpaceComplexity/Padding`** module, for later reuse by Ladner's padding;
- `Hierarchy` may import it, and the maintainer then closes `SPACE_linear_ne_NP` in a small PR.

This PR lands the **statements only**. The proof of `mem_SPACE_padLang` is a fill, briefed after
this gate closes.

**The PR:** #219 on `lean/epad-statements`, head `7cd74fff` (full hash in the bundle header). It
consists of the change `b635f73b` and merges of the campaign. It adds
`TCSlib/Complexity/SpaceComplexity/Padding.lean` (77 lines) and its line in the
`SpaceComplexity` facade.

## The statements (verify)

```lean
def padLang (L : Language Bool) (pad : ℕ → ℕ) : Language Bool :=
  {y | ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true)}

theorem mem_padLang_iff {L : Language Bool} {pad : ℕ → ℕ} {y : List Bool} :
    y ∈ padLang L pad ↔ ∃ x ∈ L, y = pairEncode x (List.replicate (pad x.length) true) :=
  Iff.rfl

theorem mem_SPACE_padLang {L : Language Bool} {S T : ℕ → ℕ} (C d : ℕ) (hL : L ∈ SPACE S)
    (hST : ∀ n, S n ≤ T (2 * n + 2 + C * (n + 1) ^ d)) (hT : ∀ m, m + 1 ≤ T m) :
    padLang L (fun n => C * (n + 1) ^ d) ∈ SPACE T := by
  sorry
```

All three are in namespace `Complexity`. The module imports `SpaceComplexity/Basic` only, which
brings in `SPACE` and, through `Encoding`, `pairEncode`. `|pairEncode x w| = 2|x| + 2 + |w|`
(`Turing.length_pairEncode`), so the padded length is `2n + 2 + C (n + 1)^d`.

**Why it should be true (the fill's route, in the docstring's sketch).** Let `M` decide `L` in
`c · S` cells. On input `y`:
1. Check that `y` is `pairEncode x w` with `w = 1^{C (|x|+1)^d}`, and reject otherwise. This
   needs `O(|y|)` cells, which `hT` pays for at every length, valid or not.
2. Run `M` on `x`, copied or read through a bounded input device, within `c · S |x|` cells,
   which `hST` pays for at the padded length.

`DecidesInSpace` asks for `O(T |y|)` on every input. Invalid inputs cost only the check.

## Brief for the auditor

1. **Truth and form:** is `mem_SPACE_padLang` true as stated, for every `S`, `T`, `C` and `d`?
   Check in particular:
   - `C = 0` and `d = 0`;
   - a non-monotone `T`;
   - invalid inputs;
   - the empty `x`;
   - that `DecidesInSpace` needs the bound at every input length.

   Are the hypotheses the natural ones? Is anything stronger than needed in a way that would
   block the reuse the ruling intends (Ladner's padding, which is time-based and would need its
   own statement)?
2. **The consumer:** does the statement give exactly the hypothesis that `Hierarchy`'s private
   `sph_linear_ne_NP_of_padding` consumes at `S n = n² + 1`, `T n = n + 1`, `C = 1` and `d = 2`?
   Answer through `mem_padLang_iff` only, with no unfolding of `padLang` (rule 10);
   `evidence/probe/`.
3. **Public text:** are the docstrings accurate and attributed, and is the module docstring
   complete?

## Repository-side attestations (verify or challenge)

- **Consumer probe** (`evidence/probe/EPadProbe.lean.txt`, `.out`). The probe:
  - copies the module's text inline;
  - derives `sph_linear_ne_NP_of_padding`'s `hpad` hypothesis from `mem_SPACE_padLang`
    through `mem_padLang_iff` and `Set.ext`, with `n² + 1 ≤ 2n + 2 + (n + 1)² + 1` from
    `Nat.pow_le_pow_left` and `omega`;
  - instantiates the edge case `C = 0`, `d = 0`;
  - prints `mem_padLang_iff`'s axioms.

  It elaborates with **exit 0**. The only `sorry` warning is the statement's own, and
  `mem_padLang_iff` depends on no axioms.
- **Replay** (`evidence/merged-tree/`): `replay-lep2` at `7cd74fff` (the new module and the
  facade), chained from the campaign snapshot after #216: **2 modules, 0 failed**. The one
  `sorry` warning is `mem_SPACE_padLang`'s. The static check finds 0 mismatches. #217 and #211
  merged afterwards. Neither touches `Padding`'s import closure (`SpaceComplexity/Basic` and
  upstream).
- **Lint** (`evidence/lint/`):
  - The policy linter on `Padding` gives 0 findings.
  - The campaign lint on `SpaceComplexity` gives 0 FAIL, 82 WARN over 113 files. The one new
    WARN is check 8 ("public def without a lemma beside it: `padLang`"). That check recognizes
    only `padLang_…` names. The definition's published characterization is
    `mem_padLang_iff`, in the `mem_SPACE_iff` pattern of `SpaceComplexity/Basic`. This is
    disclosed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

The severity guide is in `campaign/standards/TEMPLATE.md`. Findings are copied verbatim into
`campaign/gates/110-epad-statements/findings.md`. The gate closes when it has zero blockers and
zero majors.

**Deliver your findings as a downloadable Markdown file named `epad-statements-findings.md`** (the
findings table and the verdict line, no other wrapping), and also paste its content in your reply.
