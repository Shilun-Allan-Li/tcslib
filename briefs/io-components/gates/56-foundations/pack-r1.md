# Gate 56 · the iO foundations gate: PRs #374, #378, #384, #380 · round 1

Round 1. The auditor is Codex, under the standing ruling of 2026-11-11 (Codex for audits and reviews). **Gate 56** is the
one Codex gate for the four in-house foundation PRs that the iO-components jobs and the efficiency remediation build
on. Gates 51 and 52 audited the io-phfe and io-sprg deliveries built on these PRs (their base, `iO/phase-a-base`), not
the PRs themselves; Gate 51's G51-04 touched the contract only as used by a consumer. These PRs have had no external
audit until now.

| PR | Branch → base branch | Head | Commits · diff | Content |
|---|---|---|---|---|
| **#374** | `foundations/subexp` → `cryptography/pass-shelat-ch2-4` | `cbce64d1c135c710b7c036968ed9d4f21414aa72` | 1 · 2 files, +303 | `Foundations/Subexponential.lean`: `SubexpSmall`, `SubexpHard` |
| **#378** | `foundations/coin-sampling` → `foundations/subexp` | `3473adda66d9c61c51ba640ed4c701e5cde0b6b1` | 10 · 10 files, +1,892 | the sampler bridge: `Games/Closeness`, `CoinSampling/{Basic,Buckets,Transfer,Asymptotic,Instances,Efficiency}` and the facade |
| **#384** | `foundations/coin-contract` → `foundations/coin-sampling` | `40e12f64293833056e311ab7aaf5a62fb3006353` | 4 (one a merge of #378's readers) · 2 files, +464 | `CoinSampling/Contract.lean`: `DrawSamplable`, `CoreComputable`, `SamplesEfficiently` |
| **#380** | `foundations/realization` → `foundations/subexp` | `cdc0934f36365533d410607d0664a0570ae92679` | 1 · 2 files, +254 | `Asymptotic/Realization.lean`: `NUPPT.RealizesOn` and its link lemmas |

**Stack.** #374 → (#378 → #384) and #374 → #380.

**`iO/phase-a-base`** = `5382668bc9cc496355c83e7b77909d9647e089b3` merges all four. Its `TCSlib` tree is
`9dcf16477970d330a6202fad6ca2fd1e0e6d5405`, and each of its 15 changed paths is blob-equal to the PR head that owns
it (`verification-r1.zip:merge/phase-a-composition.txt`).

**Merge base with the records:** `a2bf4bac0d545fce1fcb4014ef12b44f9651a658` (`TCSlib` tree `849ee945…`, Lean-equal to
olean snapshot #10).

**The diffs** in this directory are taken against each PR's base branch head, which is also its merge base (GitHub's
three-dot view):
- `pr374.diff.txt`: `a2bf4bac..cbce64d1`;
- `pr378.diff.txt`: `cbce64d1..3473adda`;
- `pr384.diff.txt`: `3473adda..40e12f64`;
- `pr380.diff.txt`: `cbce64d1..cdc0934f`.

**Records pin:** the commit that files this directory, `briefs/io-components/gates/56-foundations/`.
- The records tip replayed is `53e430b68cbe22416312a4f80bbc3426c71cf86d`. Its `TCSlib` tree is
  `745bf4b494b6581a5666ef9ca0a6e735a68ddcef`, the same Lean as Gate 54's replayed tip.
- During staging the records branch moved, records-only:
  - to `057fe893a12ed627b21a1a81c09e6451e8752b56`: the Gate 55 staging and pin, and a work-in-progress commit of part
    of this directory (not the pin);
  - then to `b0d5438dadb2d1c92f46489039b9fa452eb01a13` (EF-H11 records).
  - 0 paths changed under `TCSlib/`, `TCSlib.lean`, `audits/`, `scripts/`, the toolchain, the manifest and the
    lakefile.
  - The `TCSlib` tree is the same.
  - `merge-tree(057fe893, 5382668b)` has the same `TCSlib` tree, `6a724839…`.
  
  `source-head-r1.json` records `53e430b6` as `tip_at_staging`; read that field as "the tip replayed".
- Since `a2bf4bac`, the records side changed 12 Lean paths (GSW 6b statements, U12/U13, `LWE/BitEncoding`,
  `LWE/Ratio`). None of them is a foundation path.

**Merged tree:**
- `git merge-tree --write-tree 53e430b6 5382668b` is clean: tree `4d0347941c394f6fe1ed88ec067814bcfc1fb6f9`, `TCSlib`
  tree **`6a724839672002fcf75c0c36e79564cbea62d0ba`**.
- The maintainer replayed it as the scratch commit `ed165e99431951c466668f0b235edd12b457b3cb` (parents `53e430b6` and
  `5382668b`; **on no ref, never pushed**).

**Mathlib** `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, **Batteries** `39260e31b7b3f7f05643da95242463b462dc05f1`,
toolchain `leanprover/lean4:v4.25.0` (the manifest is unchanged by all four PRs).

Paths below are under `TCSlib/Cryptography/` unless they start with `TCSlib/` or `briefs/`. `CS/` is
`TCSlib/Cryptography/CoinSampling/`. Line numbers are at the PR heads, which equal the merge's blobs.

## How this gate runs (standing rules 17 and 18)

- **Cloud, reading only.** Every input is in the repository: the records branch at the pin, the four PR branches and
  `iO/phase-a-base`. Nothing is needed from Seyoon's machine, and nothing is on the exchange.
- **No Lean, no cache.** The auditor does not run `lean`, `lake` or `lake exe cache get`, and builds nothing. The build
  evidence is the maintainer's: the PR reports, the #384/#387 landing record, and this directory's merged-tree
  verification (`verification-r1.md`, `verification-r1.zip`). The audit grades that evidence by reading it.
- **Tools:** Python as `python3 -I`; `git`, `sha256sum`, `unzip` and reading tools only. Mathlib and Batteries source
  may be read at the pinned revisions, never built.
- **Sources.**

  | Status | Sources |
  |---|---|
  | Ingested under `blueprint/src/references/` (read and quote these) | **PS10** ch. 2 (`pass-shelat-2010-ch2.raw.md`: Def 23.4 l. 98, Def 24.6, Def 26.8 l. 207, Lemma 51.17 l. 1313); ch. 5–8 tags are graded against `briefs/pass-shelat-ch5-8/ingests/ps10-cite-check-final-r1/REPORT.md` (Def 181.1 is checked OK there). **Pei16** (`peikert2016-lattice-survey.raw.md`; Defs 4.2.1, 4.2.3). **Sho04** (`shoup-2004-sequences-of-games.raw.md`; §1.1). **AB09** ch. 7 (`arora-barak-ch07-randomized-computation.raw.md`; §7.2) |
  | **Not ingested, and not attached** | **JLS26** (Def 2.1, §1.1, Remark 2.1, proof of Prop 4.1); **Lem19** (arXiv 1805.10941v4 §3.2 Alg. 4, Lemma 2.1); **Gar26** (Def 1.4, Exercise 1.1, §1.2); **GJLS21** (Def 4.3) |

  A finding that depends on the wording of a source in the second row is marked **UNVERIFIED-SOURCE**. Such a finding
  is graded only on the internal consistency of the statement with the citation text the records quote:
  - `subexp/REPORT.md` and the docstrings, for JLS26;
  - `IMPL-REPORT.md` § *Citation [Lem19], verified*, for Lem19.

## Scope

**#374 `Foundations/Subexponential.lean`** (300 lines; 17 public declarations, 1 private).

| Declaration | Content |
|---|---|
| `SubexpSmall c μ` | `∃ n₀, ∀ n ≥ n₀, \|μ n\| ≤ 2^(−n^c)`, with real powers |
| `SubexpHard adv` | `∃ c > 0, ∀ D, SubexpSmall c (adv D)`, over any adversary type `α` |
| Readers | `subexpSmall_iff`, `subexpHard_iff` (both `Iff.rfl`), `subexpSmall_iff_eventually` |
| Closure | `.mono`, `.mono_exponent`; `.add`, `.const_mul`, `.mul_pow` (from `c` to any `c' < c`, given `0 < c`) |
| Negligibility | `SubexpSmall.negligible`, `SubexpHard.negligible` |
| Re-indexing | `.comp_of_rpow_le` for `SubexpSmall` and `SubexpHard` (exponent `a·c` under `n^a ≤ ℓ n`) |
| The estimate | `eventually_const_mul_rpow_mul_two_rpow_neg_le` and the private `tendsto_rpow_mul_two_rpow_sub` |
| Non-vacuity | `subexpSmall_zero`, `subexpSmall_two_pow_neg` |

Ruling: the decision log `IOComponentsPlan.md`, row 2026-11-18 *Subexponential security (Seyoon)*. Report:
`briefs/io-components/subexp/REPORT.md`.

**#378 the sampler bridge** (8 modules, 146 public declarations plus 3 private readers).
- **The modules:**
  - `Games/Closeness`: `ProbComp.Close ε`, `OutputsSubset`;
  - `CS/Basic`: `CoinSampler Ω s`, the mixture identity, `pi`/`prod`, `ofRejection`;
  - `CS/Buckets`: `bucket N s` [Lem19], `ofEquiv`, `RatSeed`/`weighted`;
  - `CS/Transfer`: `draw`, `drawD`, closeness and output-inclusion transfer;
  - `CS/Asymptotic`: `drawSlack`, negligible and `SubexpSmall`;
  - `CS/Instances`: `zmod`, the LWE noise and seeds, LWE challenge transfer;
  - `CS/Efficiency`: `UniformSampler`, `toNUPPT`, `bucketRaw`, `polyTimeComputable_bucketRaw`, `bucketSampler`;
  - the facade.
- **Rulings:** the decision log rows *Sampler-bridge rulings (Seyoon)*, Q1–Q11.
- **Records:**
  - design `briefs/io-components/sampler-bridge/design-r1.md` and `Skeleton.lean`;
  - report `IMPL-REPORT.md`, which lists 11 deviations from the skeleton and the disclosed overlaps.
- **Landing edit `3473adda`** (Q-L2-1 (b), Q-L2-2): three `rfl` readers, `bucketSampler_Ω`, `bucketSampler_enc_cast`
  and `bucketSampler_fail`.

**#384 the contract** (`CS/Contract.lean`, 460 lines, 38 public declarations).
- **The definitions:** `DrawSamplable`, `CoreComputable` and `SamplesEfficiently`, with readers,
  `samplesEfficiently_iff_exists` (design-r3 §1.2's one-existential form), projections and `.intro`.
- **Closure:** `coreComputable_id`, `.map`, `.map_output`, `.pair` and `.congr`, plus the promoted `DrawSamplable.comap`,
  `samplesEfficiently_comap` and `drawSamplable_restrict`.
- **Non-vacuity:** `BoundedModulus`, `modulusWord`, `residueEnc`, `drawSamplable_residue` and
  `samplesEfficiently_residue`, plus the promoted `natToList_two_pow`, `polyTimeComputable_twoPowWord` and
  `seedModulusWord` with four readers.
- **Ruling:** Q-E1 (A) (`briefs/io-components/sprg/rulings.md`, `phfe/rulings.md`). Report:
  `briefs/io-components/contract/REPORT.md`.
- **Landing edits** (`briefs/efficiency-gaps/wave1/EF-D1/final-r1/landing-r2.md`):
  - `f96ae32e`, the promotions (EF-D1-W2 (B), EF-H11-R5 (A), DL-66);
  - merge `21f549c2` of #378's readers;
  - `40e12f64`, a proof-only re-proof of `drawSamplable_residue` through those readers (Q-L2-1 (b)).

**#380 `Asymptotic/Realization.lean`** (250 lines, 14 public declarations).
- **The predicate:** `NUPPT.RealizesOn B enc c R := B.coins = c ∧ ∀ m x r, r.length = c.eval m →
  B.runAtL m (enc m x) r = R m x r`.
- **Readers**, among them the verdict lemma `distinguisherL_eq`; `realizesOn_of_forall` and `.congr`.
- **Non-vacuity:** `realizesOn_self`, `realizesOn_self_take`.
- **The link "targets ⇒ realisers":** `exists_realizesOn_reparam_pre_post`, `exists_realizesOn_of_preTarget` and
  `_id`.
- **Rulings:** sPRG Q-S9 (A) = PHFE Q5 (A), and Q-S11 (A). Report: `briefs/io-components/realization/REPORT.md`.

**Out of scope** (mention only if something in scope depends on it):
- the consumers: the io-sprg and io-phfe deliveries (Gates 51 and 52), #387 (EF-D1) and EF-H11;
- the records side of the merge (Gates 46 and 53);
- the follow-ups that the reports already schedule: the Q8 move of the mixture identity into
  `Asymptotic/Sampling.lean` after S2-A, `close_iff_epsClose_dist`, the shared `PolyExpr` majorant,
  `uprob_apply_coord`'s move, and the Complexity owner PR for `BinArith.lt/sub/mod` (DL-70);
- products of draws (Phase B).

## Rulings and records in force

1. **Rule 15** (`briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2):
   - every honest algorithm is proved efficient **uniformly**: `PolyTimeComputable`, or `∃ A, A.Uniform ∧ A.Computes f`,
     **never a bare `∃ A : NUPPT, A.Computes f`**;
   - every reduction is a proved non-uniform PPT machine;
   - efficiency is baked into the definitions;
   - a missing efficiency proof is at least a major.
2. **Q-E1 (A):** consumers must reuse `DrawSamplable`, `CoreComputable` and `SamplesEfficiently`, and there is no
   local sampler contract.
3. **Gate 51 G51-04 and its ruling R3** (`briefs/io-components/gates/51-phfe-statements/findings-r1.md`; decision log
   *Gate 51 rulings (Seyoon)*).
   - **The finding:** a `pubGen_eff` target used a sampler parameter word without κ. Because `DrawSamplable` indexes
     `U.Ω` and `U.enc` by the word alone, that target forced equal group widths across parameters.
   - **R3:** κ-prefix the sampler parameter maps (`fun κ π => NUPPT.advInput κ (y κ π)`) unless the existing word is
     proved to determine κ.
   - **The maintainer's check then:** io-sprg's words carry unary κ or ℓ.
4. **Sampler-bridge rulings Q1–Q11** (decision log, 2026-11-18):
   - Q1–Q3: a per-sampler decoder, exact on success; a per-experiment `ProbComp.Close ε`; default-value fallback;
   - Q4: `x mod N`;
   - Q5: slack bits `t`, default κ;
   - Q6: uniform on finite types, other laws as pushforwards;
   - Q7: the new area plus `Games/Closeness`;
   - Q8: the mixture identity beside the old lemma, sequenced after S2-A;
   - Q9: no `BB1Machine.draw` retrofit now;
   - Q10: the modulus as input;
   - Q11: one PR, 8 modules.
5. **Realisation rulings:** Q-S9 (A) = PHFE Q5 (A); Q-S11 (A). The maintainer accepted the length-restricted body
   (decision log row *Shared `Asymptotic/Realization.lean` written*).
6. **Subexponential ruling** (decision log): a predicate with the constant quantified before the adversary, closure
   under sums and polynomial factors, ⇒ `Negligible`, and re-indexing by a polynomial parameter.
7. **Efficiency-gap rulings** (`PassShelatChapter5-8Plan.md`):
   - EF-W1-R (A): readers go into their owner files; the maintainer adds our own files' readers as landing edits;
   - EF-D1-W2 (B) and EF-H11-R5 (A): the promotions into `Contract.lean`;
   - Q-L2-1 (b), Q-L2-2 and Q-L2-3 (a), in the rows of 2026-11-19.
8. **Rule 10** (`policy.md` §1; DW-10 W1–W7).
   - Another file's TCSlib definition is read only through published readers. Core and Mathlib definitions may reduce
     in `rfl`/`decide`/`show` steps.
   - The canonical **coe-A** seal is the check.
   - DL-70 records `Efficiency`'s three private `BinArith` readers as bounded debt.
9. **Duplication** (`policy.md` § *Duplication*; `briefs/pass-shelat-ch5-8/duplication-ledger.md` DL-66 and DL-70;
   precedents G44-01, G45-01, G48-01). Disclosure is not acceptance. An undisclosed or unaccepted re-proof or
   restatement of a public TCSlib, Batteries or Mathlib lemma, including an inline re-derivation, is a **major**.
10. **Policy** (`policy.md`): formula docstrings with the statement prose first; a source tag or a glue statement; a
    `**Proof sketch.**` for every nontrivial proof; files of 150–600 lines as the target and under 1,000.

## Staging observations (the maintainer's, from staging and `verification-r1`)

- **S-1 · undisclosed Rule-10 residues in #378 (in-house finding).** The merged-tree coe-A seals
  (`verification-r1.md` §6) give 0 on 6 of the 10 owners, and `CS/Efficiency` gives exactly its known 3 (DL-70).
  **8 further errors in 5 declarations** are not recorded anywhere: the #378 report and body seal only `Efficiency`,
  and the landing sealed only `Efficiency` and `Contract`.

  | Owner | Errors | Declarations (line) | What each reads |
  |---|---:|---|---|
  | `CS/Buckets` | 1 | `ofEquiv_dec` (194) | `CoinSampler.congr` (`Basic`) |
  | `CS/Instances` | 1 | `zmod_dec` (61) | `CoinSampler.congr` (`Basic`) |
  | `CS/Transfer` | 6 | `close_draw_bind` (108–109), `close_drawD_bind` (126, 131), `outputsSubset_drawD` (153) | `ProbComp.Close` and `OracleComp.OutputsSubset` (`Games/Closeness`), as functions |

  - **The readers exist in #378:** `CoinSampler.congr_dec`, `bucket_dec`, `ProbComp.close_iff` and
    `OracleComp.outputsSubset_iff`.
  - **The fix probe:** one-line, proof-only edits through these readers seal each of the three owners to **0**
    (`verification-r1.zip:seal/fixprobe/`).
  - **No PR has been changed.** A landing edit on #378 is the expected remedy, as for Q-L2-1.
- **S-2 · PR #378's body overstates reuse.** Its *Reuse* paragraph lists `OneWay.statClose_pi` and
  `Nat.count_modEq_card`. Neither name occurs in the 15 files (`checks/pr378-reuse-claims.txt`), and `IMPL-REPORT.md`
  says both were "not needed".
- **S-3 · stale gate lines in two bodies.** The bodies of #374 and #380 say "Audited together with the first
  iO-components statements gate". Gates 51 and 52 used `iO/phase-a-base` as their base and did not audit these PRs;
  this gate is that audit.
- **S-4 · the κ question (G51-04 class).**
  - **What the contract does:**
    - `DrawSamplable` reads the law through `U.Ω (y κ π)`, `U.enc (y κ π)` and `U.sampler (y κ π) (c.eval κ)`, so κ
      reaches the draw only through the coin count;
    - `UniformSampler.raw_layout` receives `1^κ` on the layout, but `Ω`, `enc` and `sampler` cannot depend on it;
    - `CoreComputable` gets κ through `NUPPT.advInput κ`.
  - **The consequence:** a consumer whose draw type or encoding depends on κ beyond what the word and `c(κ)` determine
    gets a **false (unprovable) target**, not a vacuous one. That is what happened at G51-04.
  - **Neither the module docstring nor `DrawSamplable`'s docstring says this.**
- **S-5 · the parameter word is unconstrained.**
  - **Nothing bounds or fixes `y κ π`:** neither its length (polynomial in κ?) nor its relation to the public input.
    `CoreComputable`'s `f` is polynomial in the length of `⟨1^κ, ⟨y κ π, encDraw d⟩⟩`, so a word of super-polynomial
    length, or one that carries precomputed data, would satisfy the core half trivially.
  - **What the docstrings say:** "the encoded public input … Nothing computes it".
  - **The only non-vacuity instance** (`modulusWord`) has length `b(κ) + 1`.
- **S-6 · two PS10 tags to check against the ingested text.**
  - **Lemma 51.17.** It is cited in `CS/Basic` and `CS/Buckets` as "rejection sampling is uniform conditioned on
    success". The ingested statement (`pass-shelat-2010-ch2.raw.md` l. 1313) is "Algorithm SamplePrime outputs a
    randomly selected n-bit prime number in time poly(n)".
  - **Definition 23.4.** It is cited for "one machine, uniform coins" in `CS/Efficiency` and `CS/Contract`.
- **S-7 · known and disclosed (for grading only).**
  - `subexpSmall_drawSlack` keeps an unused `_hc0 : 0 < c` (IMPL deviation 8).
  - `Close.simulate` needs `0 ≤ ε` (deviation 1; the skeleton statement is false without it).
  - The products of draws are deferred.
  - The unused `Fintype` binder was dropped from the contract.
  - The disclosed overlaps: the Q8 mixture identity, `uprob_apply_coord`, `polyExpr_eval_le_mul_pow`, and the three
    private `BinArith` readers (DL-70).
  - Every foundation file carries `set_option maxHeartbeats 0`, which `style_lint` requires.

## Questions for the audit

**A. #374: statement fidelity and the API.**
1. **The definitions.** Are `SubexpSmall` and `SubexpHard` the notions of [JLS26, Def 2.1 and §1.1] (UNVERIFIED-SOURCE
   unless you can quote it)? Check:
   - the constant before the adversary;
   - `c > 0`, imposed in `SubexpHard` but not in `SubexpSmall`;
   - the bound on `|μ n|`;
   - the real powers.
2. **The closure lemmas.** Are their hypotheses (`0 < c`, `c' < c`, with no sign condition on `c'`) right, and does
   `SubexpSmall.negligible` follow without circularity (via `mul_pow` at `c' = 0`)?
3. **The re-indexing.** Is `comp_of_rpow_le` the content of [JLS26, Remark 2.1]? Check its exponent `a·c`, its
   hypotheses `0 ≤ c`, `0 < a` and eventual `n^a ≤ ℓ n`, and the family version.
4. **Use against NUPPT.** Is `SubexpHard` over a generic `α` sound to instantiate at `α := NUPPT`, given the library's
   `∀ D : NUPPT, Negligible (adv D)` convention?
5. **Non-vacuity.** Is it sufficient? There is no `SubexpHard` instance, for example a zero family.

**B. #378: fidelity, design rulings and efficiency.**
1. **The bucket test [Lem19, §3.2, Alg. 4].**
   - Are `bucketDec`/`bucket` and the one-round deviation stated as the source does (UNVERIFIED-SOURCE; grade
     against `IMPL-REPORT.md`'s quotation)?
   - `fail_bucket = (2^s mod N)/2^s` exactly, also for `N = 0`.
   - `fail_bucket_le` with `b + t` coins.
2. **`CoinSampler`.** Is it "exact on success" (equal probability of every outcome), and is `fail` a derived quantity?
3. **The mixture identity** `uexp_comp_dec`, with `statClose_some` and `statClose_getD`.
4. **`ProbComp.Close ε` (Q2).**
   - Is "every `[0,1]`-valued test" the per-experiment closeness the ruling asked for?
   - Is `Close.simulate`'s `m·ε` with `0 ≤ ε` right?
   - Is `advantage_le_of_close` right?
5. **`OutputsSubset`.** Does it transfer every `AllOutputs` property (Q3)?
6. **The asymptotics.** Are `drawSlack`, `negligible_drawSlack` and `subexpSmall_drawSlack` (every `0 < c < 1` when
   `t ≥ κ`) correct?
7. **The instances.** `zmod 3 4`: is each residue 5/16 and the failure 1/16? Check the LWE seeds against [Pei16,
   Defs 4.2.1, 4.2.3].
8. **Efficiency.**
   - Is `UniformSampler` a uniform PPT in the sense of rule 15 ([PS10, Def 23.4]), with the modulus as input (Q10) and
     no κ-indexed program?
   - Is `polyTimeComputable_bucketRaw` built only from proved tooling? Read `bucketRaw_eq_binArith` and the three
     private readers.
   - Is `toNUPPT_uniform` real (empty advice)?
9. **The 11 deviations and the added glue** in `IMPL-REPORT.md` § *Deviations*: is each one acceptable?

**C. #384: the contract (rule 15).**
1. **Rule 15.** Is `SamplesEfficiently` uniform: no advice, no κ-indexed machine, no bare `∃ A : NUPPT, A.Computes`?
   Does it keep the exact law `core <$> sample Draw`, with failure `≤ 2^{-κ}` at a polynomial coin count `c(κ)` as
   the only slack?
2. **Design fidelity.** Is `samplesEfficiently_iff_exists` exactly design-r3 §1.2's predicate, apart from the dropped
   `[Fintype]` binder (`briefs/io-components/sprg/design-r3.md` §1.2)?
3. **The κ question (S-4, G51-04).** Does the contract make the G51-04 error easy to make? Should it change? The
   options:
   - (a) κ in the word by construction, i.e. `U.Ω`, `U.enc` and `U.sampler` reading `advInput κ (y κ π)`;
   - (b) a docstring and a checked reader stating that the word must determine the draw type and encoding at every κ;
   - (c) leave it as it is, since the error fails closed (an unprovable target).
   Say which you recommend and why.
4. **The word's length and content (S-5).** Must the contract bound `|y κ π|` polynomially in κ, or tie `y` to the
   public input, for `CoreComputable` to mean "efficient in κ"? Give a concrete trivialising instance if one exists.
5. **The closure lemmas.** Are `.map` (the parameter word on `h`'s input), `.map_output`, `.pair`, `.congr`, `.comap`,
   `samplesEfficiently_comap` and `drawSamplable_restrict` sound, and does each keep the uniformity?
6. **Non-vacuity.** Are `drawSamplable_residue` and `samplesEfficiently_residue` genuine (uniform `ZMod q`, `b(κ) + κ`
   coins, the modulus read from the input)? Is `residueEnc` the encoding the bucket sampler writes?

**D. #380: the reduction form.**
1. **The predicate.**
   - Does `RealizesOn` constrain exactly what a security reduction needs: encoded challenges, coin strings of length
     `c(m)`, and the reduction's advice inside `R`?
   - Is the realiser a non-uniform PPT in the sense of [PS10, Def 26.8], with polynomial advice through `NUPPT`?
2. **The body that the maintainer accepted** (only `r.length = c.eval m`). Do theorems of the form "∀ realiser ⇒
   inequality" stay meaningful, and are they not vacuous? The link lemmas supply realisers.
3. **The link lemmas.** Do they bound the advice length (`hb`) and the parameter map (`φ ≤ p`) as a non-uniform PPT
   requires? Is `B.coins = A.coins.subst p` right?
4. **Misuse.** Is any honest-algorithm use of `RealizesOn` possible without breaking rule 15? The docstrings forbid it;
   is that enough?
5. **Non-vacuity.** `realizesOn_self` is trivial. The non-trivial instance of the link (`pre := pairSndD`) was an
   uncommitted probe. Is a committed instance needed?

**E. Readers and Rule 10 (S-1).**
1. **Readers.** Does every public definition of the 10 owners have a definitional reader beside it (`rfl`/`Iff.rfl`),
   with a formula docstring?
2. **Rule-10 reads.** Read the five declarations of S-1 and confirm that each reads another file's definition. Check
   the proposed one-line fixes in `seal/fixprobe/edits.txt`. Look for any other read of another TCSlib file's
   definition that the coe-A seal cannot see: `show`/`change`/`decide` steps, or `unfold` of a foreign name.
3. **The landing readers.** Are the three `bucketSampler_*` readers `rfl` and beside `bucketSampler`, and do they read
   only their own file? Is Q-L2-2's choice (three readers, not one) justified?
4. **DL-70.** Are `Efficiency`'s three private readers exactly DL-70's bounded debt?
5. **Severity.** Grade S-1 and say whether it must be fixed before merge.

**F. Duplication.**
1. **Report the searches you ran, with hit counts,** for each new public definition and lemma, against TCSlib at the
   merge, Mathlib and Batteries. At least:
   - `SubexpSmall`, `SubexpHard` against Mathlib (`Asymptotics.SuperpolynomialDecay`, `IsLittleO` lemmas);
   - `ProbComp.Close` against `StatClose` (`Asymptotic/Sampling.lean:126`), `EpsClose` (`InformationTheory/Extractors.lean:62`)
     and `statDist`;
   - `CoinSampler` against `uniformFromBits`, `rejectionSample` and `firstHit`;
   - `encodeOption`;
   - `two_pow_sub_mod_eq` against `Nat.div_eq_sub_mod_div`;
   - `card_filter_finProdFinEquiv_symm_snd` against `Nat.count_modEq_card`;
   - `polyExpr_eval_le_mul_pow` and `subexpSmall_polyExpr_mul` against `Negligible.polyExpr_mul` and the two
     `negligible_polyExpr_mul`s;
   - `RealizesOn` against `NUPPT.Computes`, `toComp`/`toCompOn` and `Lamport/Realization`.
2. **The disclosed overlaps** (S-7). Is each acceptable as disclosed, with its follow-up scheduled?
3. **DL-66.** Are the promoted helpers' statements the originals? (`checks/promotion-stmtcmp.txt`: 9/9 EQUAL against
   `bd4c6f2d` on `land/ef-d1-lattice-families` and EF-H11's `71acf81c`. That commit is on no remote ref; its decls2 row
   is at `4e787bc23:inbox/fills/ef-h11-sharing-bgw/evidence/checks/C3-decls2.txt` on the exchange branch.) Is
   `drawSamplable_restrict` now really a one-line `comap`?

**G. The landing edits** (`landing-r2.md`).
1. Is `3473adda` exactly the three readers (decls2 3 ADDED)?
2. Is `f96ae32e` exactly the 10 additions, with no import or existing statement changed?
3. Does merge `21f549c2` take only #378's readers?
4. Is `40e12f64` proof-only?
5. Do Q-L2-1 (b), Q-L2-2 and Q-L2-3 (a) hold as recorded?

**H. Docstrings, sketches, attribution, size.**
1. Is every result tagged with a source or marked Glue, and is every nontrivial proof sketched? Check in particular:
   - the long proofs in `Subexponential`;
   - `bucketRaw_eq_binArith`, `polyTimeComputable_bucketRaw` and `drawSamplable_residue`;
   - the link lemmas.
2. Do the tags match the ingested PS10, Pei16, Sho04 and AB09 texts (S-6)? Mark the JLS26, Lem19, Gar26 and GJLS21
   tags UNVERIFIED-SOURCE unless you can quote them.
3. Are the file sizes within policy? The largest is `Basic`, at 487 lines.

**I. Evidence.**
1. **Grade `verification-r1.md` and its ZIP:**
   - the merge;
   - the start-tree state check and the 37-module replay;
   - the forced downstream rebuild;
   - the admissions, the axiom census (280 constants), the seals and the fix probe, and the lint.
2. **Grade the PR reports' check sections and the landing r2b re-check.**
3. **Binding.** Does each piece of evidence bind to the stated heads, or, for the merge, to `TCSlib` tree `6a724839`?
   A missing or non-binding piece of necessary evidence is a major.

**J. Anything undisclosed.** S-1 to S-7 are the known items.

## Deliverable

`findings-r1.md`, in this form:
- **Findings** `G56-01`, `G56-02`, …, each with: severity (blocker / major / minor / note), PR, file and declaration,
  claim, evidence (quoted lines and commands), and proposed fix.
- **A table grading S-1 to S-7.**
- **The searches you ran,** with hit counts.
- **The audited heads,** the records pin, and the verification ZIP's SHA-256 as you computed it.
- **Counts by severity.**
- **A verdict per PR:** CLEAR (zero blockers and zero majors) or HOLD.

Return it as Markdown in the chat, or as a ZIP with `findings-r1.md` at its root if you have search logs or scripts.
