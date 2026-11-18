# ef-h11-sharing-bgw: final delivery (EF-H11, efficiency wave 1)

**Head:** `edacd3c90a86f811c376104d6a03f84b506e8328`, on local branch `fill/ef-h11-sharing-bgw` (not pushed).
**Base:** IO `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`, tree `9155903018d18fbc735791f21485abaaee3e161a`.
Both checked with `git rev-parse`.
**Records pin:** `54dcb3021a389831e7f94c3f82616cb7594fa574`. All nine COMMON §1 inputs match their SHA-256 there.
**Merge with the records tip** (information only): `git merge-tree --write-tree HEAD 54dcb302…` is clean, tree
`15a912b55d5d89db57b5f2d33a19d90b931645f6`.

**Status, in short.** All three files and the two facade edits are built. They compile with 0 errors and 0 `sorry`,
and every axiom is standard. Three lines stop on **E-SCOPE**:
- **W1.** `SecretSharing/Defs.lean` has no readers for `Scheme.Correct`, `LocalReconstruct` and `PerfectPrivacy`.
  Four transfer lemmas therefore read those definitions. Exactly that read is confined by the seal, and a
  three-line reader patch removing it is verified.
- **W2.** `degreeReduce` and `recombine` have no readers. So the multiplication gate stops one rewrite short of
  `bgwEval_mul`. A two-line patch closing it is verified.
- **W3.** No registered host evaluates an encoded arithmetic circuit. The whole-circuit evaluator is therefore not
  built; the host contract is given below.

## 1. Commits

| # | Commit | Content |
|---|---|---|
| 1 | `56ade7282be0725db8d270c19527566e6d601c32` | File A (interface) + File B (Shamir instance) + `SecretSharing.lean` facade (= checkpoint 1, exchange `bfa0f10f`) |
| 2 | `145f998acadfbe02b7716dbbac22c29e47561be6` | File C (BGW) + `MPC/BGW.lean` facade |
| 3 | `dbf9319f3aebd0a4db90bd86567f4df905e848e7` | Rule 10: `encWords []` read through `encWords_nil` (found by the seal) |
| 4 | `3045b0a06362803b3e1231462da011acc165c95d` | readers `partyEmb_apply`, `coinModulus_eq` (lint check 8) |
| 5 | `9fefdd3cc99064ec2bcecd93af9f4deda83484bb` | rename `powStep` → `dealerPowStep` (would shadow `BinArith.powStep`; C10) |
| 6 | `edacd3c90a86f811c376104d6a03f84b506e8328` | docstring: drop an anchor the brief does not list (`[PS10, Def 23.4]`) |

All commits are unsigned (`gpgsig` count 0). The author and committer data are in `patches/COMMITS.tsv`.
`git diff --stat` against the base lists only the brief's five files: 1,750 insertions, 0 deletions.

## 2. Environment, pool, who did what

- **Preflight** (`evidence/logs/preflight.log`):
  - `nproc` 4. There is no cgroup v2 memory file, so headroom = `MemAvailable` 15.0 GiB.
  - 21.5 GB free on ext4. A re-check before the second cache fetch is logged there too.
- **Cache:**
  - Store absent before the first fetch.
  - Narrowed fetch for the 74 roots of the files' closure: 2,340 files, rc 0.
  - Before the root sweep, the 379 roots of the whole `TCSlib` closure: 1,267 more downloaded, 3,607 decompressed,
    rc 0 (`cache-get-root.log`).
  - Packages match the manifest after both fetches. ABSENT: doc-gen4, UnicodeBasic, BibtexQuery, MD4Lean.
    0 empty oleans.
- **Bootstrap:** the closure of the new files, 109 modules, all rc 0 (`evidence/build/bootstrap-summary.txt`).
- **Pool:** `min(4, 15 GiB/4 GiB) = 3` slots (flock), shared by lead and sub-agent. Peak RSS per module is
  2.94 GB (`ShamirEfficient`). History is in `evidence/logs/pool.log`.
  - While the bootstrap's `DetMod` was still compiling, up to 4 Lean processes ran, which equals `nproc`.
    MemAvailable stayed above 10 GiB.
- **Sub-agent `bgw`** (`evidence/subagents/bgw/`) wrote File C in its own worktree and olean tree, with
  `.lake/packages` linked. It compiled only through the shared pool. The lead re-checked it, edited two docstrings,
  and committed it.
- **Lead:** everything else, including all `lake`/cache work and every commit.
- **Incident (recorded, not a finding):**
  - The first root-sweep attempt failed in modules outside the narrowed Mathlib closure (missing Mathlib roots).
  - A scratch clone for C13 then filled the disk.
  - The sweep was stopped, the clone removed and the exchange clone made sparse. The remaining roots were fetched
    and the sweep restarted at the final head. The attempt's logs are in `evidence/build/root-attempt1/`.

## 3. Target map

| Brief target | Declarations (file) |
|---|---|
| A: `ShamirParams`, encoding + readers | `SecretSharing.ShamirParams`, `.encode`, `.encode_eq`, `.pairFstD_encode`, `.pairFstD_pairSndD_encode`, `.pairSndD_pairSndD_encode` (A) |
| A: `EfficientScheme` (share / listed reconstruction poly-time, dealer coins) | `SecretSharing.EfficientScheme` with fields `share_poly`, `reconstruct_poly`, `dealer_efficient`; `SecretSharing.DealerSamples`, `dealerSamples_iff` (A) |
| A: link to the abstract `Scheme` | field `scheme : ∀ π, Scheme …`; `Scheme.restrict` (+ `restrict_share`, `restrict_reconstruct`, `restrict_reconstruct_of_eqOn`) (A) |
| A: `Correct`/`PerfectPrivacy` through the existing notions | `EfficientScheme.Correct`, `.LocalReconstruct`, `.PerfectPrivacy` (+ `_iff`); transfer `Scheme.restrict_correct`, `restrict_localReconstruct`, `restrict_perfectPrivacy`, `AccessStructure.threshold_map_auth` (A) |
| B: `shamirEfficient`, correctness, privacy (transferred) | `Shamir.shamirEfficient`, `shamirEfficient_scheme`, `_access`, `_correct`, `_localReconstruct`, `_perfectPrivacy`; `shamirScheme` (+ `_eq`, `_share`, `_reconstruct`, `_correct`, `_localReconstruct`, `_perfectPrivacy`), from `Shamir.correct`, `Shamir.localReconstruct`, `Shamir.perfectPrivacy` (B) |
| B: coefficient draw | route **bucket**: one draw over `Fin (p^{k−1})` decoded to base-`p` digits: `coinEquiv` (+ `_apply`, `coeff_coinEquiv`, `eval_coinEquiv`), `dealerSamples_shamir` (from `samplesEfficiently_residue`), `shamirAdm`, `coinModulus`, `dealerWord`, `dealerPowStep` (B); `samplesEfficiently_comap` (A) |
| B: evaluation and Lagrange mod p on `BinArith`, Fermat inverses | `shareRaw` (+ `_spec`, `polyTimeComputable_shareRaw`, `shareStep`, `shareState`); `recombineRaw` (+ `_spec`, `polyTimeComputable_recombineRaw`, `lagStep`, `lagTerm`, `recStep`, `lagNum`, `lagDen`, `recombine_toFinset_eq`) (B); residue layer `resWord`, `addModW`, `subModW`, `mulModW`, `invModW` with `_resWord`/`polyTimeComputable_` lemmas (A) |
| C: `shamirResharer`, `polyTimeComputable_reshare…` | `MPC.BGW.shamirResharer`, `shamirResharer_reshare`, `shareRaw_shamirResharer`, `polyTimeComputable_reshare`, `reshare_dealerSamples` (C) |
| C: per-gate steps + agreement | input `resWord_bgwEval_input`; const `resWord_bgwEval_const`; add `addModW_bgwEval`; smul `mulModW_bgwEval_smul`; mul `mulModW_bgwEval_mul`, `recombineRaw_reshare`, `recombineRaw_shareRaw` (C); last step to `bgwEval_mul`: **W2** |
| C: whole-circuit evaluator | not built: **W3** (host contract below) |

## 4. Statement changes (old form → new form, reason)

1. **The interface carries more than the brief's sketch.**
   - The brief proposed `share_poly`, `reconstruct_poly` and `dealer_efficient : SamplesEfficiently …` directly.
     The interface now also has dependent types `Party/Secret/Share/Rand : Pub → Type`, an `access` field and an
     admissibility predicate `Adm : ℕ → Pub → Prop`.
   - `dealer_efficient` is `DealerSamples Rand Adm encPub encRand`, meaning:
     - an efficient sampler with the identity core, at the public parameters admissible at `κ`;
     - its parameter word is computed by one `PolyTimeComputable` map from `⟨1^κ, encPub π⟩`.
   - Reason: a sampler with `2^{−κ}` failure needs the coin space bounded by `κ`. The bucket sampler's parameter
     word is the numeral of the coin space (`p^{k−1}`), not the scheme's parameter word, so the honest dealer must
     compute it, and the definition requires that.
2. **Reconstruction from a listed set.**
   - Input: `⟨π, encWords [⟨i, f i⟩ : i ∈ l]⟩` for a duplicate-free `l` listing `A`.
   - Output: the secret `(scheme π).reconstruct A f`.
3. **Encodings.**
   - The parameter word is `⟨p, ⟨1^k, n⟩⟩`, with `p` and `n` as little-endian `Nat.bits` and `k` unary. The share
     loop runs `k − 1` rounds, so a binary `k` would not give polynomial time.
   - Residues and party labels are `Nat.bits` of the representative. Coins are `Nat.bits r` with `r < p^{k−1}`.
4. **Shamir instance.**
   - The brief's `shamirEfficient : EfficientScheme` is parametric in the coin-bound polynomial `b : PolyExpr`, with
     `Adm = shamirAdm b` (`p^{k−1} ≤ 2^{b(κ)}`).
   - Parties are `Fin n`, with party `i` the residue `i + 1`. This follows [PS10, Prot 154.4], as in `Shamir.scheme`'s
     deviation note.
5. **Resharer.**
   - `shamirResharer π ρ : Resharer (ZMod π.p) (π.k − 1)`, with explicit coins `ρ i x : Fin (p^{k−1})`.
   - Its efficiency is `polyTimeComputable_reshare`: one poly-time map, witness `shareRaw`.
   - Its coins: `reshare_dealerSamples`.
6. **Gate steps.**
   - The sub-agent stated them as agreement lemmas of the existing leaf machines with `bgwEval`'s clauses. It did not
     add wrapper definitions, which would only restate `addModW`/`mulModW`/`recombineRaw` (the duplication rule).
   - The input and constant steps are the identity map.
7. **Residue layer moved from B to A.** File B reached 1,105 lines (over the 1,000 limit). The scheme-independent
   modular arithmetic on words (`resWord`, `addModW`, `subModW`, `mulModW`, `invModW`) went to File A, namespace
   `TCSlib.SecretSharing`.

No target was weakened. All targets that are not blocked are proved.

## 5. Checks

| Check | Result | Evidence |
|---|---|---|
| **C1 Build** | 3 new modules + 2 facades + downstream `MPC`: rc 0, 0 errors (both forms), 0 `sorry` warnings. Each source SHA-256 is bound to `git show edacd3c9:<path>` | `build/final/summary.txt`, logs |
| **C2 Downstream** | importers of the changed facades: `TCSlib/Cryptography/MPC.lean` rc 0 (C1); `TCSlib.lean`: **incomplete**. The root module is unreachable on this host: 3 unrelated modules need `PFR` oleans. 596 of 1,459 modules checked: 593 rc 0, 3 PFR (§5.1) | `build/root-summary.txt`, `build/root/` |
| **C3 Statements** | `decls2.py`: 141 ADDED, 0 removed / changed; facades have imports and docstring only (C7). `StmtAx` probe prints all 187 new constants (incl. structure projections) with full name and type | `checks/C3-decls2.txt`, `probes/StmtAx.{lean,out}` |
| **C4 Admissions** | 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/`@[simp]` in the new files. No existing declaration changed, so the base's `sorry` set is unchanged | `checks/C4-forbidden.txt` |
| **C5 Axioms** / **H11-P3** | all 187 constants ⊆ {`propext`, `Classical.choice`, `Quot.sound`}; 0 `sorryAx` | `probes/StmtAx.out` |
| **C6 Rule 10** | see §5.2 | `rule10/` |
| **C7 Frozen files** | facades: 0 differences outside the listed insertions; control (one altered character) = exactly 1 difference per facade | `checks/C7.txt`, `checks/allowed-*.txt` |
| **C8 Lint** | `style_lint.py` on the 3 new files: 0 findings. The facades' 6 findings (missing `set_option`s) are pre-existing and identical at the base. `campaign_style_lint.py --check8b`: base 92 FAIL / 103 WARN over 542 files (= the maintainer's IO figures); head 92 / 103 over 545. FAIL/WARN line sets identical | `checks/C8-*.txt` |
| **C9 Sizes** | Efficient 550 lines / width 98; ShamirEfficient 965 / 100; BGW/Efficient 236 / 100; facades 40 / 97, 29 / 96 | `checks/C9-sizes.txt` |
| **C10 Clashes** | 187 new full names vs IO (= base), #377 head `7563734a…`, S2-A `cleanup/stage2-s2a` = `c119a3c4f1d8642b1328740f1d1d1165a92f5567`, in `TCSlib/` and `audits/`: **0 full-name clashes** (82 short-name hits, all in other namespaces) | `checks/C10.txt`, `checks/new-names.txt` |
| **C11 Reuse** | §6 | `checks/C11-searches.txt` |
| **C12 Probes** | H11-P1, H11-P2 below | `probes/H11P.{lean,out}` |
| **C13 Reproduction** | `git am` of `patches/` at the base, with `COMMITS.tsv`'s committer data, in a scratch clone: all 6 hashes reproduced; `src/` equals the head byte for byte | `checks/C13.txt` |

### 5.1 Root sweep (C2): incomplete on this host

The changed facades are imported by two modules:
- `TCSlib/Cryptography/MPC.lean`: rc 0, 0 errors (C1, `build/final/`).
- the root `TCSlib.lean`.

No other module imports the new files.

**The root step is incomplete** (addendum: "deliver the final with the root step marked incomplete, its log tail
and the last module checked").
- The sweep over the whole closure (1,459 modules, head `edacd3c9`, pool 3) checked 596 modules: 593 rc 0, 3 rc 1.
- The 3 failures are `CommunicationComplexity/NewmanTheorem/{Newman, Entropy/Basic,
  FuncDisjointnessLowerBound/HardSample}`, each with `unknown module prefix 'PFR'`. They import the `PFR` package,
  whose oleans the Mathlib cache does not provide; building them would need `lake build`.
- So the root module `TCSlib`, which imports them, cannot be checked on this host whatever the order. The sweep was
  stopped with 863 modules not reached.
- Last module checked: `TCSlib/Complexity/TuringMachine/Build/NDCombinators`.
- None of the 3 failures is downstream of this job's files. Evidence: `build/root-summary.txt`,
  `build/root/pool-summary.txt`, `build/root/pool-out-tail.txt`, one failing log.

### 5.2 Rule 10 (C6)

**Seal method.** I used the gate-04 package's tools (`collect_body.lean`, `seal.py`, `scan.py`, records pin
`54dcb302…`) on the three new files at the head. Candidates came from the automatic collector:
- A: 20 candidates;
- B: 41 candidates (40 sealed, 1 already irreducible);
- C: 17 candidates;
- 0 generated-equation-lemma references.

The package seals in one mode only. The "A/B, strict/coe" variants named in COMMON C6 are not defined in the inputs I
was given, so I ran the package's seal as shipped and did not invent variants (see question EF-H11-W4).

**Results.**
- **B and C:** PASS with every candidate sealed (`rule10/seal-plain/`).
- **A:** FAIL on exactly 5 error lines, in 4 declarations:
  - `Scheme.restrict_reconstruct_of_eqOn`
  - `restrict_localReconstruct`
  - `restrict_correct`
  - `restrict_perfectPrivacy`

  These read `Scheme.LocalReconstruct`, `Scheme.Correct` and `Scheme.PerfectPrivacy` (frozen `Defs.lean`), which
  have **no published readers**. With exactly those 4 declarations unsealed for exactly those 3 names, A passes
  (`rule10/seal-excl/`, `rule10/unseal.json`).

  This is **E-SCOPE W1**. No compliant proof exists: proving that any scheme is `Correct` (etc.) needs the
  definition's body.
- **The fix is verified** in a scratch tree (`scope-requests/W1-*`):
  - three `Iff.rfl` readers beside the definitions in `Defs.lean` (`correct_iff`, `localReconstruct_iff`,
    `perfectPrivacy_iff`);
  - A's proofs rewritten through them.

  With that, A passes the full seal with no exclusion (`rule10/seal-scopepatch/`).
- **Explicit-unfold scan:** 0 lemma-list hits, 0 `show`/`change` at seal failures, 0 proof-term equation-lemma
  references (`rule10/unfold-scan.log`).
- **Paired controls**, one per new owner, appended in a scratch copy (`rule10/controls-*`). The foreign `rfl` read
  passes unsealed and fails sealed exactly once:
  - A: `Scheme.LocalReconstruct` by `Iff.rfl`;
  - B: `scheme.share` by `rfl`;
  - C: `resWord` by `rfl`.

  The reader read passes sealed:
  - A: `threshold_auth`;
  - B: `scheme_share`;
  - C: `resWord_eq`.
- **Reader census** (every foreign definition the files read; candidates in `rule10/candidates/*.txt`):

| Foreign definition | Reader used |
|---|---|
| `BinArith.add/sub/mul/div/mod/powMod` | `add_pairEncode`, `sub_pairEncode`, `mul_pairEncode`, `div_pairEncode`, `mod_pairEncode`, `powMod_pairEncode` |
| `BinArith.beq` | `beq_def` |
| `BinArith.encWords`, `countW`, `decWords` | `encWords_cons`, `encWords_nil`, `countW_eq`, `decWords_encWords` |
| `BinArith.forLoop` | `forLoop_pairEncode`, `polyTimeComputable_forLoop`, `forLoop_bound_of_ctx` |
| `PrefixByLength.take` | `take_def`, `polyTimeComputable_takePrefixByLength` |
| `LogProg.bitsVal` | `bitsVal_bits` |
| `pairEncode`, `pairFstD`, `pairSndD` | `pairFstD_pairEncode`, `pairSndD_pairEncode`, `length_pairEncode`, `length_pair_components_le`, `length_pairFstD_le`, `length_pairSndD_le` |
| `NUPPT.advInput` | `advInput_eq` |
| `PolyExpr.eval` | `eval_add`, `eval_const` |
| `Encoding.BinaryArith.toLE`, `fromLEPoly` | `toLE_eq_natBits`, `fromLEPoly_pairEncode`, `polyTimeComputable_toLE`, `polyTimeComputable_fromLEPoly` |
| `Candidates.natToList`, `NumberTheory.listToNat` | `listToNat_natToList` |
| `CoinSampling.SamplesEfficiently`, `modulusWord`, `residueEnc` | `samplesEfficiently_iff_exists`, `.map_output`, `.congr`, `samplesEfficiently_residue`, `modulusWord_eq`, `residueEnc_eq` |
| `Shamir.scheme`, `poly` | `scheme_share`, `poly_eval`, `correct`, `localReconstruct`, `perfectPrivacy`, `isSharing_share` |
| `Shamir.recombine` | `recombine_eq_eval_interpolate`, `recombine_eq_reconstruct` |
| `MPC.BGW.bgwEval` | `bgwEval_input`, `_const`, `_add`, `_smul` |
| `AccessStructure.threshold` | `threshold_auth` |
| `Scheme.Correct`, `LocalReconstruct`, `PerfectPrivacy` | **MISSING**: `correct_iff`, `localReconstruct_iff`, `perfectPrivacy_iff` (W1) |
| `MPC.BGW.degreeReduce`, `Shamir.recombine` (body) | **MISSING**: `degreeReduce_apply`, `recombine_eq` (W2) |
| Own files across each other (A ← B ← C) | `resWord_eq`, `*_resWord`, `polyTimeComputable_*`, `shareRaw_spec`, `recombineRaw_spec`, `coinEquiv` readers, `ShamirParams.*_encode`, `dealerSamples_shamir`, … (the seals of B and C pass with A's and B's definitions sealed) |

Transparent abbreviations read through their bodies, as policy §1 allows: `Shamir.Party`, `Shamir.label`,
`CoinSampling.BoundedModulus`. Mathlib definitions appear only in `change` steps (`Lagrange.basis`,
`Lagrange.basisDivisor`, `degreeLTEquiv`), never in `simp`/`rw`/`unfold`.

### 5.3 Brief probes

- **H11-P1** (`probes/H11P.out`), at `p = 7`, `k = 2`, `n = 3`:
  - shares for all secrets and coins agree with the reference `sec + x·q`, which is `Shamir.scheme`'s share at
    `k = 2`;
  - reconstruction (`recombineRaw`) from every 2-set and from the 3-set returns the secret, for all 49
    (secret, coin) pairs: `true`/`true`/`true`.
  - The formal agreement with `Shamir.scheme` is `shareRaw_spec`. The probe compares against its value formula,
    because `Shamir.scheme` is noncomputable.
- **H11-P2**, a multiplication gate at `p = 7`, `d = 1`, three parties, `a = 3`, `b = 5`:
  - local products `[0, 1, 4]`;
  - party `j`'s recombination of the received re-sharings is `[5, 2, 6]`. This equals the `degreeReduce`
    formula `∑ λ_i · reshare_i(j)` with `λ = (3, 4, 1)`: `true`.
  - Every 2-set recombines the reduced vector to `a·b = 1 (mod 7)`.
- **H11-P3:** C5.

## 6. Overlap and reuse (C11)

**Searches** (`checks/C11-searches.txt`: commands and hit counts, at the base):

| Search | Hits |
|---|---|
| `PolyTimeComputable` in SecretSharing/MPC | 0 |
| `powMod` consumers | 5 |
| modular inverse definitions | 14 |
| Lagrange/interpolation machines | 0 |
| Horner / polynomial evaluation machines | 2, both Mathlib-level in Hermite polynomials |
| residues as `Nat.bits` words | 0 |
| product samplers | 1, a docstring |
| scheme restriction | 1, a docstring word |
| `SamplesEfficiently` reindexing | 0 |
| `Fin p ≃ ZMod p` | 4 |
| `finFunctionFinEquiv` | 2 |
| Fermat-inverse lemmas | 0 |
| the brief's names | 0 |

I also grepped Mathlib names, and ran `exact?` where noted in development.

**Must-reuse items and where they are used.**
- `Scheme`, `Scheme.Correct`, `LocalReconstruct`, `PerfectPrivacy`: A (`restrict`, transfer); the
  `EfficientScheme` predicates are defined through them.
- `PerfectPrivacy.card_view_eq`: not needed; no counting form is stated.
- `Shamir.poly`, `poly_eval`, `scheme`, `scheme_share`, `correct`, `localReconstruct`, `perfectPrivacy`: B
  (`shareRaw_spec`, `shamirScheme_*`).
- `natCard_coins_view`: not needed.
- `vecScheme`: not used; no vector secrets.
- `IsSharing`, `isSharing_share`: C (`shamirResharer`).
- `recombine`, `recombine_eq_reconstruct`, `recombine_eq_eval_interpolate`: B (`shamirScheme_reconstruct`,
  `recombine_toFinset_eq`), C.
- `recombineCoeff`: only through W2.
- `Resharer`: C.
- `degreeReduce`, `bgwEval_mul`: W2.
- `bgwEval` and its other equations: C.
- `isSharing_degreeReduce`, `bgwEval_isSharing`, `bgwEval_recombine`: not needed for efficiency statements.
- `Circuit`: C.
- `CoinSampling`: `SamplesEfficiently` and its readers (`samplesEfficiently_iff_exists`, `.map_output`, `.congr`);
  `samplesEfficiently_residue` (whose draw half is `bucketSampler`).
- `CoreComputable.map`: used through `SamplesEfficiently.map_output`.
- `CoinSampler.pi`, `fail_pi_le`: not used (bucket route).
- `BinArith` `add`, `sub`, `mul`, `div`, `mod`, `powMod`, `beq`; `forLoop` (host H16, all three loops),
  `polyTimeComputable_forLoop`, `forLoop_bound_of_ctx`; `encWords`, `countW`: A and B.
- `polyTimeComputable_iterate`, `getW`: not needed; `forLoop` covers the loops.
- `Encoding.BinaryArith` `toLE`, `fromLEPoly`: B (dealer).
- `NUPPT.ofPolyTimeUniform`: not needed. Every honest map is stated `PolyTimeComputable`; the dealer's machine is
  the contract's `UniformSampler`.

**Near-relatives (path:line, relation, reason).**
- `BinaryArith/DetMod.lean:197`, `:275`, `:300`: inline Fermat pivot inverse through `powMod`/`sub`.
  `invModW` (A) is **the first public modular-inverse map**, composed the same way (Q-H11-2 A). It is cited in its
  docstring.
- `Candidates/DiscreteLogHardcore.lean:1011` (`dlb_invMod`, private): inverse through `xgcdStr` under the
  `ArithmeticFP` hypothesis, general modulus. I did not prove `xgcdStr` (EF-H1's).
- `Hashing/FromDiscreteLog/Sampling.lean:47` `residueFinEquiv` (public, with `residueFinEquiv_val`):
  - `finZModEquiv` (B) is its inverse direction, stated with explicit cast formulas;
  - `dealerSamples_shamir` uses the same `(ZMod.finEquiv q).symm` as that definition's body.
  - Not imported: it would pull the discrete-log hashing stack into `SecretSharing`.
  - Proposed: harvest one public `Fin p ≃ ZMod p` with both readers into a shared place.
- `Encoding/Modular.lean:51` `encodeVector`: residues as fixed-width MSB numerals, no machines. `resWord` is the
  `BinArith` little-endian format, which the arithmetic readers need. Different format, not a restatement.
- `Complexity/Randomized/RandomBits.lean:225`: `finFunctionFinEquiv` used for bits. `coinEquiv` uses it for base-`p`
  digits.
- `CoinSampling/Contract.lean`, "Products of draws": no product sampler exists. The single bucket draw over
  `p^{k−1}` avoids one.
  - `samplesEfficiently_comap` (A, glue) reindexes an efficient sampler along a map of public inputs. It is a
    candidate for `Contract`.
- `MPC/BGW/Privacy.lean:73` `dealtInputs`: dealer-made input sharings with abstract coins. `shamirResharer` is the
  per-value counterpart with explicit coins.

No exact restatement was found or delivered. No private helper is copied across files (the new files declare no
`private` names).

## 7. Scope requests and escalations

- **E-SCOPE W1 (Rule 10; frozen `SecretSharing/Defs.lean`).** Add three readers beside the definitions:
  - `Scheme.correct_iff`, `Scheme.localReconstruct_iff`, `Scheme.perfectPrivacy_iff`, each `Iff.rfl`. The patch is
    `evidence/scope-requests/W1-defs-readers.patch`.
  - Then rewrite A's four transfer proofs through them (`W1-efficient-after-readers.diff`, 22 lines).
  - Verified in a scratch tree: `Defs` and A compile, and A passes the full seal with no exclusion.
  - Until then, the four declarations are named seal exclusions, confined to those 3 definitions.
- **E-SCOPE W2 (Rule 10; frozen `SecretSharing/Sharing.lean`, `MPC/BGW/Protocol.lean`).** Add two readers:
  - `recombine_eq : recombine A f = ∑ i ∈ A, recombineCoeff A i * f i`;
  - `degreeReduce_apply : degreeReduce R A u j = ∑ i ∈ A, recombineCoeff A i * R.reshare i (u i) j`.
  - Both are `rfl`, in `W2-readers.patch`.
  - With them, the multiplication gate's full agreement holds and passes the seal:
    `recombineRaw ⟨p, [⟨i, R.reshare i (u i) j⟩]⟩ = resWord (bgwEval R A inp (a.mul b) j)`, where
    `u = bgwEval a * bgwEval b`. The proof is three rewrites (`W2-bgw-mul-agreement.diff`).
  - Until then, C proves the gate up to `recombine A fun i => R.reshare i (u i) j`.
- **E-SCOPE W3 (no registered host; Q-H11-1 A).** The whole-circuit evaluator (party `j`'s output share from an
  encoded `Circuit F ι`) needs two things that do not exist:
  - **(i) An encoding of `Circuit F ι`.** A prefix word of gate records (kind, constant, input index), with a
    reader `encCircuit_eq` and an injectivity lemma, in `MPC/ArithmeticCircuit.lean` or a sibling.
  - **(ii) A tree-evaluation host**, registered in `machine-library-design.md` §14 (H1/H18/H19 do not fit: H18 and
    H19 are pure functions, not machines).
    - Contract: for a polynomial-time gate body `g` on `⟨ctx, ⟨gate record, ⟨left value, right value⟩⟩⟩` whose
      output is at most `|ctx|` long, `treeEval g ⟨ctx, encCircuit C⟩` evaluates `C` bottom-up (a post-order
      stack walk over the record word) and equals `enc (Circuit.foldEval …)`.
    - `polyTimeComputable_treeEval`, with round count `≤ |encCircuit C|` and state length
      `≤ |encCircuit C|·(|ctx| + c)`.
    - Generic in the value encoding and the gate body.
  - **For BGW,** a multiplication gate is interactive: the party's evaluator also reads, per multiplication gate,
    the listed re-sharings it received. So its input is
    `⟨π, ⟨input shares, ⟨encCircuit C, received lists in gate order⟩⟩⟩`, and its agreement theorem with `bgwEval`
    also needs W2.

## 8. Questions for Seyoon

- **EF-H11-W1. `Defs.lean` readers (W1).**
  - **A (recommended):** approve the three `Iff.rfl` readers beside the definitions (patch verified). A follow-up
    commit rewrites A's four transfer proofs through them, which removes the seal exclusions.
  - **B:** accept the four named exclusions as recorded debt.
- **EF-H11-W2. BGW readers (W2).**
  - **A (recommended):** approve `recombine_eq` (`Sharing.lean`) and `degreeReduce_apply` (`Protocol.lean`), each
    `rfl`. A follow-up adds `recombineRaw_bgwEval_mul` (verified).
  - **B:** leave the gate at the recombination step.
- **EF-H11-W3. Whole-circuit evaluator (W3).**
  - **A (recommended):** commission the circuit encoding and the tree-evaluation host as a statement item
    (contract in §7); the evaluator follows in wave 2.
  - **B:** record BGW's whole-circuit efficiency as out of scope.
- **EF-H11-W4. Seal variants.** COMMON C6 names seals "A and B, strict and coe (coe-A canonical)", which the shipped
  gate-04 tools do not define.
  - **A (recommended):** accept the package's seal as run here (plain plus named exclusions, controls, scan).
  - **B:** send the variant definitions, and I rerun.

## 9. Evidence manifest

`evidence/SHA256SUMS` lists every file under `evidence/`. The main directories:
- `logs/`: preflight, cache store, both cache fetches, roots, package checks, `pool.log`.
- `build/`:
  - bootstrap order and summary;
  - `cp1/` (checkpoint-1 builds);
  - `final/` (C1 at the head);
  - `order-root.txt`, `root/` and `root-summary.txt` (C2);
  - `root-attempt1/` (the stopped first attempt).
- `rule10/`: candidates, seal plain / exclusion / scope-patch / controls, `unseal.json`, unfold scan.
- `checks/`: C3, C4, C7, C8, C9, C10, C11, C13, merge-tree.
- `probes/`: `StmtAx` and `H11P` sources and outputs.
- `scope-requests/`: W1 and W2 patches and diffs.
- `subagents/bgw/`: the sub-agent's logs and notes.
