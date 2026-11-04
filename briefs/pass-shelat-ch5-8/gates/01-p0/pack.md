# Gate 01 (Pass–shelat ch. 5–8, prong zero): external audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#183](https://github.com/Shilun-Allan-Li/tcslib/pull/183)
into `main`, at its head `789cf450527ff6b8c779161e555f04093080b88d` (base: `main` at
`06e61e912eedc2bce49b3ccff77bb9c4a7e18579`). One combined gate (statements, definitions, sketches,
proofs and docstring citations), by the user's ruling: the PR has no `sorry`, and its proofs are
short. The deliverable is **`gate01-p0-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source text is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010, as a PDF. The audited items are on PDF pp. 163–166 (book pp. 151–154,
§6.1) and PDF pp. 193–196 (book pp. 181–184, §8.3). Book page numbers are also the item numbers'
prefixes (for example, Definition 181.1 is on book p. 181).

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 change: definitions, theorem statements,
their docstrings and proof sketches, against the cited source. The proofs are machine-checked;
do not review tactic scripts for correctness, except where a disclosure below asks for it. The
failure modes you are hunting are:

1. **Infidelity:** a definition that does not mean what the cited source means.
2. **Trivialization:** a definition or statement satisfiable for degenerate reasons (vacuous
   hypotheses, a class that collapses, an encoding that makes a theorem empty).
3. **Wrong strength:** a statement subtly weaker or stronger than the docstring claims. Check
   boundary cases: the empty type, `k ≤ 0`, `ε < 0`, an empty class of sources, one-point types.
4. **Missing hypotheses:** finiteness, nonemptiness, positivity.
5. **Debt:** duplication of existing proved material in the library (see the attestations).
6. **Attribution:** every source-derived declaration carries a `[Tag, location]`; every deviation
   from the source is declared, with its reason ([`policy.md`](policy.md) §2–3, in the bundle).

For **every definition** in scope: restate it in your own mathematical English *before* reading
its docstring, compare your restatement with the cited source item, and report any daylight. For
**every theorem**: say in 1–3 sentences whether the statement is what its docstring claims.
Attempt at least **three adversarial instantiations**: concrete pathological objects plugged into
the definitions, to check they behave as the theory intends. Propose machine-checkable sanity
theorems you think are missing.

Do not give a blanket approval. An empty findings table must come with the per-definition
restatements that justify it.

## Scope

| Item | Where |
|---|---|
| New Lean (all declarations audited) | `TCSlib/InformationTheory/Entropy.lean` (195 lines), `TCSlib/InformationTheory/Extractors.lean` (206 lines) |
| Facade (imports and contents list only) | `TCSlib/InformationTheory.lean` |
| Docstring-only edits (audit the added citations and deviation notes; code unchanged) | `TCSlib/Cryptography/SecretSharing/Defs.lean`, `TCSlib/Cryptography/SecretSharing/Shamir.lean`; the bundle also has the diff against `main` |
| Context, already on `main` (not under audit; read to check the new statements' meaning) | `TCSlib/InformationTheory/FinDist.lean`, `StatisticalDistance.lean`, `UniversalHashing.lean`, `LeftoverHash.lean`; `TCSlib/Cryptography/SecretSharing/Interpolation.lean` |
| Source | [PS10] §6.1 (Def 152.1, Lem 153.2, Fact 153.3, Prot 154.4, Prop 154.5) and §8.3 (Defs 181.1, 181.2, 182.3, 183.4, 183.5; §8.3.3) |
| Standards | `policy.md` (attribution and proof-sketch rules) |
| Out of scope | tactic proofs, except the disclosures below; the design of the context files |

### The new public declarations (33)

`Entropy.lean`, namespace `TCSlib.InformationTheory.FinDist`:
- **definitions:** `shannonEntropy` (Def 182.3), `maxProb`, `minEntropy` (Def 183.4), `IsSource`
  (Def 183.5), `IsFlatSource` (Def 183.5), `flat`;
- **theorems:** `shannonEntropy_nonneg`, `shannonEntropy_uniform`, `shannonEntropy_uniform_bits`,
  `le_maxProb`, `maxProb_le_iff`, `maxProb_pos`, `le_minEntropy_iff`, `isSource_iff_hasMinEntropy`,
  `IsSource.mono`, `IsFlatSource.isSource`, `flat_apply`, `isFlatSource_flat`, `isSource_uniform`.

`Extractors.lean`, namespace `TCSlib.InformationTheory`:
- **definitions:** `FinDist.probTrue`, `EpsClose` (Def 181.1), `IsExtractor` (Def 181.2),
  `IsStrongExtractor`, `seededSources`;
- **theorems:** `FinDist.probTrue_sub_probTrue`, `abs_probTrue_sub_le_statDist`,
  `statDist_le_of_epsClose`, `epsClose_iff_statDist_le`, `EpsClose.symm`, `EpsClose.trans`,
  `IsExtractor.mono`, `IsStrongExtractor.isExtractor_seeded`, `isStrongExtractor_of_isUniversal`
  (§8.3.3).

One private lemma: `sum_sub_eq_zero` (`Extractors.lean`).

## Attestations

Maintainer execution claims, stated so you can verify or challenge them. The evidence logs are in
the bundle under `evidence/`.

1. **Elaboration.** `scripts/lean_check_tree.sh` checked, one module at a time and into a fresh
   olean tree, the 18 modules of the touched files' downstream closure (without the root module
   `TCSlib`), in dependency order. All 18 passed: exit 0, no `error:` line and a fresh olean each,
   with 0 warnings and 0 `sorry` (`evidence/replay-head.log`).
2. **Axioms.** `#print axioms` for each of the 22 new theorems, and for `TCSlib.Shamir.correct`,
   `perfectPrivacy` and `natCard_coins_view`, prints exactly
   `[propext, Classical.choice, Quot.sound]` (`evidence/axioms.log`).
3. **Docstring-only.** For `SecretSharing/Defs.lean` and `Shamir.lean`, the text with comments
   stripped is byte-identical to `main` (`evidence/docstring-only.log`).
4. **Lint.** `scripts/style_lint.py` reports 0 findings on the two new files. The 8 findings on
   the other three touched files are on `main` already: the facade's three missing options, and
   five undocumented lemmas in the Shamir files (`evidence/style-lint.log`).
5. **Duplication.** The new names and concepts were searched across `main` and the branches
   `cryptography/pass-shelat-ch2-4`, `complexity/arora-barak-ch3-4` and `cryptography/garg-ch1-3`,
   and in the pinned Mathlib (`evidence/duplication.log`).
   - **No copy found.** Mathlib's total variation is measure-theoretic, not on `FinDist`.
   - **One parallel concept, disclosed:** `TCSlib.Cryptography.StatClose` on the unmerged ch. 2–4
     branch, a closeness of *samplers* (maps from uniform seeds into a possibly infinite type).
     `EpsClose` is a closeness of `FinDist`s. Different carriers; a bridge is owed when the ch. 2–4
     layer integrates with `main`.
6. **Line width.** No line over 100 characters in the touched files.

## Disclosures: definitions read through their bodies

The campaign's rule 10 asks proofs to read another file's TCSlib definitions only through
published equations. `main` has no such rule, but the departures are disclosed:
- `abs_probTrue_sub_le_statDist` and `statDist_le_of_epsClose` read
  `statDist p q = ½ ∑ |p a - q a|` by `rfl`. `StatisticalDistance.lean` publishes no equation.
- `IsStrongExtractor.isExtractor_seeded` uses that `hashPair f X` is definitionally the pushforward
  of `uniform S × X` along `(s, x) ↦ (s, f s x)`, as `LeftoverHash.lean` defines it.
- `le_minEntropy_iff` closes by `rfl` against `HasMinEntropy`'s body (`∀ a, p a ≤ 2 ^ (-k)`).

## Known deviations (declared in the docstrings; verify they are benign, and flag any others)

- `shannonEntropy`: base 2 only. [PS10] defines entropy for any base and calls base 2 Shannon
  entropy.
- `IsFlatSource`: defined as uniform on `2^k` points, with `k : ℕ`. [PS10]'s "additionally" (it
  is also a `k`-source) is proved, not assumed (`IsFlatSource.isSource`).
- `IsExtractor`: the domain and range are arbitrary finite types, not `{0,1}^n` and `{0,1}^m`.
- `IsStrongExtractor`: [PS10] §8.3.3 is a heading with no text. The definition follows
  [Vad12, Def 6.13], and `isExtractor_seeded` reads it in [PS10, Def 181.2]'s terms.
- `SecretSharing.Scheme`: [PS10] asks `Share` and `Recon` to be p.p.t.; efficiency is not
  modelled. [PS10]'s `Recon` takes `k` indexed shares; here it takes a set of parties and a share
  assignment, with `LocalReconstruct`.
- `Scheme.PerfectPrivacy`: a bijection of the coins, stronger than [PS10, Def 152.1, item 3]'s
  "statistically close".
- `Shamir.scheme`:
  - it works over any field, with every nonzero element a party. [PS10, Prot 154.4] uses `ℤ_p`,
    `p > n`, and the parties `1, …, n`; the docstring claims [PS10]'s scheme is a restriction of
    this one and its claims are special cases;
  - the typo in [PS10] (`n − 1` coefficients up to `a_n tⁿ`) is corrected to degree `k − 1`.

## Specific questions

1. **Def 152.1 versus `Scheme`, `Correct` and `PerfectPrivacy`.**
   - [PS10]'s privacy clause says "statistically close", with no security parameter in sight. Is
     perfect privacy (identical distributions) a faithful strengthening, or does [PS10] intend
     something the library's form misses?
   - Is the threshold `Correct` (any set of at least `k` parties) a faithful reading of item 2's
     "any `k` shares"?
2. **The restriction claim on `Shamir.scheme`.** Check that [PS10]'s statements for subsets of
   `{1, …, n}` really are instances of `correct` and `perfectPrivacy` when `F = ZMod p` with `p`
   prime and `n < p`. In particular, the labels `1, …, n` must be nonzero and distinct mod `p`,
   and "fewer than `k`" must match `¬ (k ≤ #B)`.
3. **`EpsClose` versus Def 181.1.** [PS10] quantifies over deterministic, unbounded distinguishers
   with outputs in `{0,1}`. Is `D : α → Bool` that class? Would allowing randomized distinguishers
   change anything? (It should not; argue it.)
4. **`epsClose_iff_statDist_le` at the boundary.** Check it for `ε < 0` (both sides false?),
   `ε = 0` (`p = q`?), and a one-point type.
5. **`IsExtractor` with degenerate classes:**
   - the empty class (every function is an extractor: intended?);
   - `ε ≥ 1` (every function is an extractor: intended?);
   - `β` with one element.

   Should any of these carry a hypothesis, or is the vacuity harmless and as in [PS10]?
6. **`minEntropy` and `le_minEntropy_iff`.** Does `-log₂(maxProb p)` equal [PS10]'s
   `minₓ log₂(1/Pr[X = x])`? Note that points of probability zero have infinite surprise, and the
   minimum is taken over all points.
7. **`IsSource` with a real `k`, `IsFlatSource` with a natural `k`.** Is this split faithful to
   Def 183.5? Is anything lost by not allowing flat sources for non-integer `k`?
8. **The leftover hash bridge.** Are the error bound `½ √(|β| · 2^(-k))` and the strong (seeded)
   form what a reader of [PS10] §8.3.3 would expect? Is `seededSources` with `isExtractor_seeded`
   a faithful way to see a seeded extractor as a [PS10, Def 181.2] extractor?
9. **Shannon entropy conventions.** Is `negMulLog` (`0 · log(1/0) = 0`) the right convention?
   [PS10] writes `H(x)` in places for `H(X)`; the Lean uses the distribution throughout.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong statement;
- **major:** a statement is fixable but materially misleading as it stands, or accumulated debt
  (failure mode 5) that the gate may not close over without explicit human acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.
