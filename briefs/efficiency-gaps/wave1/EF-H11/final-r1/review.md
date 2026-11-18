# EF-H11 `ef-h11-sharing-bgw` · final r1 · maintainer review (phases 1 and 2)

**Verdict: ACCEPT WITH LANDING EDITS, conditional on ruling EF-H11-R1.** There is no blocker and **one
major (EFH11-F01)**, so nothing was landed and no PR was opened (dispatch rule: land only with no
blocker and no major).

- **EFH11-F01 (major, Rule 10).** Four transfer lemmas in `SecretSharing/Efficient.lean` read the
  frozen `Scheme.Correct`, `Scheme.LocalReconstruct` and `Scheme.PerfectPrivacy` by definition.
  - The canonical coe-A seal fails there with 5 errors. The worker disclosed this as E-SCOPE W1, but
    COMMON §4.3 says "a missing reader is a scope request, never an unfold".
  - The fix is the worker's verified W1 patch: three `Iff.rfl` readers in the frozen `Defs.lean`, plus
    four proof rewrites.
  - I replayed it, with W2, as a scratch landing-edit variant. Under coe-A the three new owners and
    `Defs` then have **0 errors**.
  - It needs Seyoon's grant (EF-H11-R1), because `Defs.lean` is outside the brief's files.
- **Everything else passes.**
  - Integrity: 6/6 patches reproduce, unsigned; `src/` equals the head.
  - Statements: decls2 gives 141 ADDED, 0/0.
  - Rule 15: uniform `PolyTimeComputable` share and reconstruction, with `p`, `1^k` and `n` on the
    input; dealer coins in `SamplesEfficiently` form; no bare `NUPPT`.
  - Shamir correctness and privacy are transferred from `Shamir.correct`, `localReconstruct` and
    `perfectPrivacy`.
  - The BGW resharer and every gate step are done; the multiplication gate stops one rewrite short
    (W2). The whole-circuit evaluator is E-SCOPE (W3).
- **The replay** on snapshot #11 (merge of `iO/phase-a-base` with the records tip):
  - 23/23 modules rc 0, with 0 errors and 0 `sorry`, the root `TCSlib` and both `Checks` included;
  - 217 stored constants with standard axioms;
  - B and C seal at 0 errors under coe-A; paired controls all OK;
  - lint unchanged.
- **Four minors** (F02–F05) and eight info notes. F02 is closed by the second landing edit, LE-h11-w2.

Reviewed 2026-11-18, 10:20–11:30 UTC, on records branch `cryptography/pass-shelat-ch2-4` (tip at the
end `744441c3a538be2df525b4216b71ff8dbfce6cf5`, Lean-equal to `bff0567b`). Phase 2 is in `phase2.md`.
The evidence is `ef-h11-final-r1-evidence.zip`, whose SHA-256 is in `evidence-SHA256SUMS`.

## What was reviewed

- **Delivery.** `inbox/fills/ef-h11-sharing-bgw/` on `exchange/pass-shelat-ch5-8`, at exchange commit
  `4e787bc232b256f53d0acfd17794f908e24afc1e` ("fill ef-h11-sharing-bgw: final"; unsigned, `gpgsig` 0).
  - It was extracted by `git archive` into a fresh directory: 130 files, 3.5 MB. That is `REPORT.md`
    (381 lines), 6 patches with `COMMITS.tsv`, `src/` (5 files) and `evidence/` (115 files plus its
    manifest).
  - The worker head is `edacd3c90a86f811c376104d6a03f84b506e8328`, on base `iO/phase-a-base`
    `5ed465f62e4ae0f93ded1a1ba49e807591b589eb` (tree `91559030…`).
  - The base contains #374, #378, #384 (the contract `8e01b720`) and #380. All four are open draft
    PRs, as REST `pulls/{n}` shows.
- **Contract.** The brief `briefs/efficiency-gaps/wave1/EF-H11/brief.md`, with `../COMMON.md`,
  `../rulings.md` and `../README.md`, at records pin `54dcb302`. The rulings are Q-H11-1 (A) and
  Q-H11-2 (A).
- **Standing rules.** Handoff §2 rules 15 and 16. Rule 16 is not engaged: no local input was needed.
- **Method.** The precedent is `briefs/pairings/fills/bb1-sim/fill-final-r1/{review,phase2}.md`,
  scaled down. The phase-2 method follows the parallel EF-D1 review (`../EF-D1/final-r1/phase2.md`).

## Checks (phase 1, static)

| Check | Result |
|---|---|
| **Integrity** | Both manifests pass `sha256sum -c` (top 129 files, `evidence/` 115). Delivered paths equal each manifest exactly: none missing, none extra, no `./`. |
| **Reproduction** | `git am` at `5ed465f6`, in a sparse detached worktree with committer data per `COMMITS.tsv` and signing off, reproduces **6/6**: `56ade728`, `145f998a`, `dbf9319f`, `3045b0a0`, `9fefdd3c`, `edacd3c9`. None has a `gpgsig`. `src/` equals the head's 5 files byte for byte. |
| **Scope** | `git diff --stat 5ed465f6 edacd3c9` lists exactly the brief's 5 files: `SecretSharing/{Efficient,ShamirEfficient}.lean` (new, 550 and 965 lines), `MPC/BGW/Efficient.lean` (new, 236), and the facades `SecretSharing.lean` (+7) and `MPC/BGW.lean` (+3). That is 1,761 insertions and 0 deletions. Every existing SecretSharing/MPC file is untouched (frozen). |
| **Facades** | Imports and `## Contents` entries only (diff read in full). |
| **decls2** (pinned `fa81981a`, against the scratch merge) | **141 ADDED, 0 CHANGED, 0 REMOVED.** It is identical to the delivered `C3-decls2.txt` once the location column is dropped. |
| **Hygiene** (my `hygiene.py`) | Widths ≤ 100. 0 `sorry`/`admit`/`native_decide`/`axiom`/`opaque`/`@[simp]` (the 2 "private" hits are the word in prose). Every public declaration has a docstring. Long proofs carry a `**Proof sketch.**`; the 33-line `shamirEfficient` is a structure instance whose field proof is 16 lines. **Docstring notes: F04.** |
| **Citations** | Every anchor used occurs in the existing SecretSharing/MPC files at the base or in the brief's list: `[PS10, Def 152.1]` (items 2 and 3), `Prot 154.4`, `Prop 154.5`, `[Sha79, §2]`, `[BGW88, §3]` and `[AL17, §3–4]`. Nothing is fabricated. Commit 6 dropped `[PS10, Def 23.4]`, which the brief does not list. |
| **Clashes** | The worker's C10 covered IO, #377's head and S2-A. I re-checked the files changed since then on the records tip `744441c3`, `cleanup/stage2-s2a` `a1545eae` and `land/ef-d1-lattice-families` `bd4c6f2d` (#387). The only short-name hits are in other namespaces (`Secret`, `Correct`, `correct_iff`, `p`, LWE/SIS `encode*`), so there is no full-name clash. Only the facades and root import the new modules, and the root and both `Checks` replay with rc 0. |
| **Disjointness of the LE files** | `SecretSharing/Defs.lean`, `SecretSharing/Sharing.lean` and `MPC/BGW/Protocol.lean` are in neither `scope.tsv` nor `s2a-items.tsv`. They are unchanged on `cleanup/stage2-s2a`, the records tip and IO. None of the 11 open PRs touches a SecretSharing/MPC file. |

## Statements against the brief

The target map in REPORT §3 is accurate: I checked each row against the source. The statement changes
in REPORT §4 are all disclosed and justified, and none weakens a target.

1. **The interface fields** `Pub`, `Party`, `Secret`, `Share`, `Rand`, `access` and `Adm`, and
   **`DealerSamples`**.
   - **Why `Adm` is needed.** A sampler with failure `2^{-κ}` and polynomially many coins cannot draw
     from a coin space unbounded in `κ`. So the brief's unparametrised
     `dealer_efficient : SamplesEfficiently …` over all `π` was not satisfiable, and the worker's
     repair is genuine.
   - **The parameter word.** `DealerSamples` also requires the sampler's parameter word to be computed
     uniformly from `⟨1^κ, encPub π⟩`.
   - **A side-effect.** The interface does not force `Adm` to be eventually true. See F03.
2. **Listed reconstruction.** The input is `⟨encPub π, encWords [⟨i, f i⟩ : i ∈ l]⟩` for a
   duplicate-free `l` listing `A`.
3. **Encodings.**
   - The parameter word is `⟨bits p, ⟨1^k, bits n⟩⟩`. `k` is unary because the share loop runs
     `k − 1` rounds, so a binary `k` would not give polynomial time. This is honest and disclosed.
   - Residues are `Nat.bits` of the representative.
4. **The instance.** `shamirEfficient (b : PolyExpr)`, with parties `Fin n` and party `i ↦ i + 1`.
   This is [PS10, Prot 154.4], as in `Shamir.scheme`'s own deviation note.
5. **The resharer.** It takes explicit coins `ρ i x : Fin (p^{k−1})`.
6. **The gate steps.** They are agreement lemmas of the existing leaf machines, with no wrapper maps
   (I3).
7. **The residue layer** moved from File B to File A to keep B under 1,000 lines.

**`EfficientScheme.Correct`, `.LocalReconstruct` and `.PerfectPrivacy`** are defined **through** the
existing `Scheme.Correct`, `Scheme.LocalReconstruct` and `Scheme.PerfectPrivacy` at every `π`. There is
no second definition of either notion, and each has its `_iff` reader.

## Rule 15 (uniform forms)

- **Share.** `share_poly` is witnessed by `shareRaw`, which is `PolyTimeComputable`
  (`polyTimeComputable_shareRaw`). It is one machine for all `π`.
  - The input is `⟨π.encode, ⟨sec, ⟨r, i⟩⟩⟩`, with `p`, `1^k` and `n` all present.
  - It is a counted loop on the registered host H16, `BinArith.forLoop`, with a context-bounded
    growth envelope (`forLoop_bound_of_ctx`).
- **Reconstruct.** `reconstruct_poly` is `recombineRaw ∘ ⟨pairFstD ∘ pairFstD, pairSndD⟩`: it projects
  `p` out of the parameter word.
  - `recombineRaw` is two nested `forLoop`s with `countW` counters.
  - Its Lagrange denominators are inverted by Fermat, `invModW = powMod ⟨a, ⟨p − 2, p⟩⟩`, under
    Q-H11-2 (A). `invModW_resWord` needs `p` prime, which `ShamirParams.prime` supplies.
  - Exactness is `recombineRaw_spec` with `lagDen_ne_zero`.
- **Dealer coins.** `dealerSamples_shamir b` is `SamplesEfficiently`:
  - `samplesEfficiently_residue` (the bucket sampler, with failure at most `2^{-κ}` and the exact law
    on success);
  - reindexed by `samplesEfficiently_comap` and moved to `Fin (p^{k−1})` by
    `SamplesEfficiently.map_output`/`congr`;
  - with the identity core;
  - and with the parameter word `p^{k−1}` computed by `dealerWord b`, which is `PolyTimeComputable`.
- **No bare `∃ A : NUPPT, A.Computes`.** The only `NUPPT` use is the reader `NUPPT.advInput_eq`. There
  is no efficiency hypothesis and no `heff` pattern.
- **Non-vacuity.**
  - `shamirEfficient b` inhabits the interface with every field proved, and its encodings are
    injective (`resWord_injective`, and `Nat.bits` on `Fin`).
  - H11-P1 (`#eval` at `p = 7`, `k = 2`, `n = 3`) checks shares against `sec + x·r` and
    reconstruction from every 2-set and the 3-set, all `true`.
  - **But the interface itself admits degenerate inhabitants: F03.**

## Shamir: transfer, not re-proof

- **The typed scheme.** `shamirScheme π := (Shamir.scheme k (ZMod p)).restrict (partyEmb π) (coinEquiv π) 0`.
- **The transfers.**
  - `shamirScheme_correct` is `Scheme.restrict_correct` applied to `Shamir.correct π.k_pos` and
    `Shamir.localReconstruct`.
  - `shamirScheme_perfectPrivacy` is `Scheme.restrict_perfectPrivacy` applied to
    `Shamir.perfectPrivacy`.
  - `shamirScheme_localReconstruct` is `Scheme.restrict_localReconstruct` applied to
    `Shamir.localReconstruct`.
  - The instance theorems apply the `_iff` readers to these.
- **Nothing is re-derived.** No Lagrange or counting argument of `Shamir.lean` or `Interpolation.lean`
  is repeated.
- **The cost.** The four generic `Scheme.restrict_*` lemmas are where the definitions are read (F01).

## BGW: done versus E-SCOPE

| Item (brief, File C) | Status |
|---|---|
| Efficient resharer | **Done.** `shamirResharer π ρ : Resharer (ZMod p) (k − 1)` is `Shamir.scheme`'s share with explicit coins. `isSharing_reshare` is `Shamir.isSharing_share`. `shareRaw_shamirResharer`, `polyTimeComputable_reshare` (witness `shareRaw`) and `reshare_dealerSamples` (coins as the dealer's). |
| Input and constant gates | **Done**, as `resWord_bgwEval_input`/`_const`: the identity map on words (I3). |
| Addition | **Done.** `addModW_bgwEval`; `polyTimeComputable_addModW`. |
| Scalar multiplication | **Done.** `mulModW_bgwEval_smul`; `polyTimeComputable_mulModW`. |
| Multiplication: local product | **Done.** `mulModW_bgwEval_mul`. |
| Multiplication: degree reduction | **Done up to one rewrite.** `recombineRaw_reshare` and `recombineRaw_shareRaw` give party `j`'s recombination `recombine A fun i => R.reshare i (u i) j`. Identifying it with `degreeReduce R A u j` (`bgwEval_mul`) needs readers of the frozen `degreeReduce` and `recombine`: **E-SCOPE W2** (F02). With the worker's W2 patch, `recombineRaw_bgwEval_mul` compiles and seals at 0 errors (phase 2, LE variant). |
| Whole-circuit evaluator | **Not built: E-SCOPE W3.** No registered host evaluates an encoded `Circuit F ι`. REPORT §7 gives the host contract: a circuit encoding with readers, and a post-order tree-evaluation host for §14, plus per-multiplication-gate received lists. This is consistent with Q-H11-1 (A). |
| H11-P2 | The delivered `#eval` (a multiplication gate at `p = 7`, `d = 1`, three parties) agrees with `∑ λ_i · reshare_i(j)` with `λ = (3, 4, 1)`, and every 2-set recombines to `a·b = 1`. |

## Duplication sweep (binding)

I searched TCSlib at the base and the newer refs, Mathlib at `029db123`, and the parallel EF-D1
delivery. The search covered names and conclusion shapes for every helper of the three files, the
BGW sub-agent's File C included.

- **No exact restatement** of a public TCSlib or Mathlib lemma. No `private` copy.
- **Fermat inverse.** `pow_sub_two_eq_inv` (`a^(q−2) = a⁻¹` in `ZMod q`) has no Mathlib counterpart:
  only `ZMod.pow_card_sub_one_eq_one`, which it uses. It also has none in TCSlib; `DetMod` inlines the
  machine, not the lemma.
- **Subtraction.** `val_sub_eq_add_sub_mod`: Mathlib's `ZMod.val_sub` needs `b.val ≤ a.val`, so it is
  a different statement.
- **Residue leaves.** `addModW`, `mulModW`, `subModW` and `invModW` are the first public residue
  leaves. Their relatives are `DetMod`'s inline `mod (mul …)` and `powMod ⟨_, ⟨p−2, p⟩⟩`
  (`DetMod.lean:197`, `:275`, `:300`), as disclosed and cited.
- **`finZModEquiv`.** This is a third spelling of Mathlib's `ZMod.finEquiv`, which has no apply
  lemmas, and of the inverse of TCSlib's `residueFinEquiv` (`Hashing/FromDiscreteLog/Sampling.lean:47`).
  It is disclosed with a reason: readable values, and not importing the DL-hash stack. See I2.
- **`recombine_toFinset_eq`.** It reads `recombine` through the public `recombine_eq_eval_interpolate`
  and Mathlib's `Lagrange.basis` (a `change`, which Rule 10 allows for Mathlib). TCSlib has no
  product-formula lemma for `recombineCoeff`.
- **`samplesEfficiently_comap`.** It generalises EF-D1's `LWE.drawSamplable_restrict` (#387, draft,
  not landed). Two parallel public near-relatives are about to land: **F05**.
- **File C.** `shamirResharer` is the per-value counterpart of `BGW/Privacy.lean:73`'s `dealtInputs`;
  that is a different object. `resWord_bgwEval_input`/`_const` are `bgwEval_input`/`_const` under
  `resWord` (brief-requested; I3).
- **Recount of REPORT §6.** The cited `path:line`s check out at the base. Every must-reuse item is used
  where REPORT says, or justified as not needed.

## Recount of the worker's evidence

| Item | Recount |
|---|---|
| **C1 build** (`build/final/`) | 6 logs: rc 0; `error:` 0, `error(` 0, `sorry` 0, warnings 0. Sources are bound to `edacd3c9` (SHA-256 equal to my export: `ad53c9ab…`, `374b82fd…`, `0facb22c…`). |
| **C2 root** | Incomplete on the worker's host: `PFR` oleans are missing from the cache, so 596 of 1,459 modules were checked, with 3 PFR failures, none downstream. **Closed in phase 2:** root `TCSlib` and both `audits/*/Checks` rc 0. |
| **C5 axioms** (`StmtAx.out`) | 187 named constants, all within {`propext`, `Classical.choice`, `Quot.sound`}. There is no `sorry` control there; phase 2 adds one. |
| **C6 seals** (gate-04 package) | A FAILS on 5 lines in 4 declarations (W1); B and C PASS. The "scopepatch" run passes A. The controls show 3 NEG lines each failing sealed and passing unsealed. **Phase 2 re-ran the canonical coe-A seal: the same failure set** (F01). |
| **C8 lint** | Base 92 FAIL / 103 WARN over 542 files; head 92/103 over 545; equal line sets. `style_lint` on the 3 new files: 0. |
| **C13** | Matches my reproduction. |

## Findings

**Blockers: none. Majors: one (F01).**

| ID | Grade | Finding | Fix |
|---|---|---|---|
| **EFH11-F01** | **major** (Rule 10; COMMON §4.3, C6) | **The transfer lemmas read frozen definitions.** `Scheme.restrict_reconstruct_of_eqOn` (`Efficient.lean:115–116`), `restrict_localReconstruct` (`:122`), `restrict_correct` (`:132`) and `restrict_perfectPrivacy` (`:143`) use `intro` and function application on `Scheme.Correct`, `Scheme.LocalReconstruct` and `Scheme.PerfectPrivacy`. These are `def`s in `SecretSharing/Defs.lean` with **no published readers**.<br>• The canonical coe-A seal of `SecretSharing.Efficient` (1,121 requests) **fails with exactly these 5 errors** (phase 2).<br>• The worker disclosed it (E-SCOPE W1) and verified a patch. But it shipped the unfolds, where the rule says to stop the line and file the scope request.<br>• `shamirEfficient_correct` and `_perfectPrivacy` depend on these lemmas.<br>• **Precedent:** derand F-01 (disclosed seal failures behind missing readers in frozen files), graded major. | **LE-h11-w1**, the worker's `W1-defs-readers.patch` verbatim: `Scheme.correct_iff`, `localReconstruct_iff` and `perfectPrivacy_iff` (`Iff.rfl`) beside the definitions in `Defs.lean`, plus `W1-efficient-after-readers.diff` (6 lines in 4 proofs).<br>• Phase 2 replays it with W2 as scratch `a299c19e`: 13/13 rc 0; coe-A of `Efficient`, `ShamirEfficient`, `BGW/Efficient` and `Defs` at **0 errors**.<br>• `Defs.lean` is frozen, so this **needs Seyoon's grant: EF-H11-R1.** |
| **EFH11-F02** | minor (E-SCOPE W2, genuine) | **The multiplication gate stops one rewrite short of `bgwEval_mul`.** `degreeReduce` (`Protocol.lean:77`) and the sum form of `recombine` (`Sharing.lean:138`) have no readers. The worker handled this compliantly: it stopped at `recombine A fun i => R.reshare i (u i) j` and said so in the module docstring.<br>• **Naming note:** the proposed `TCSlib.Shamir.recombine_eq` sits beside `TCSlib.Shamir.IsSharing.recombine_eq`. The replay shows no breakage, since dot notation resolves by type, but `recombine_eq_sum` is clearer. | **LE-h11-w2:** the readers `degreeReduce_apply` and `recombine_eq` (renaming to `recombine_eq_sum` is recommended), plus `recombineRaw_bgwEval_mul` in `BGW/Efficient.lean`, with a real docstring in place of "(Scope-request probe)".<br>• Phase 2 LE variant: rc 0; `BGW/Efficient` coe-A 0 errors; `Sharing` and `Protocol` keep exactly their pre-existing failures (I1).<br>• It touches 2 frozen files: **EF-H11-R2.** |
| **EFH11-F03** | minor (rule 15, interface non-vacuity) | **`EfficientScheme` admits degenerate inhabitants.**<br>• (a) The encodings `encParty`, `encSecret`, `encShare` and `encRand` are unconstrained, so constant encodings make `share_poly` and `reconstruct_poly` trivial.<br>• (b) `Adm` is unconstrained. With `Adm := fun _ _ => False`, `DealerSamples` holds vacuously (`{π // False}` is empty; any `UniformSampler` witnesses it).<br>• So "no instance without the proof" holds by convention, not by the definition.<br>• The Shamir instance is genuine (injective encodings, a real sampler). But with a constant `b`, `shamirEfficient b` only ever admits the `π` with `k = 1` or `p^{k−1} ≤ 2^b` (finitely many `(p, k)` with `k ≥ 2`), and nothing records that `b` must grow.<br>• Part (a) follows the brief's own sketch, which EF-D1's accepted `encodeSeed` also shares. Part (b) is the side-effect of the disclosed `Adm` repair. | Statement item (**EF-H11-R3**): add `encParty_injective`, `encSecret_injective`, `encShare_injective` and `encRand_injective` fields, and `adm_eventually : ∀ π, ∀ᶠ κ in atTop, Adm κ π`. Shamir discharges them with `resWord_injective`, `Nat.bits` injectivity, and an unbounded `b` (e.g. `b = κ`). |
| **EFH11-F04** | minor (COMMON §4.6, policy §2) | **Docstrings.**<br>• 96 declarations carry neither a source tag nor a "Glue" note: readers, machines, loop invariants and length envelopes (list in `phase1/hygiene.txt`).<br>• 10 readers are the bare label "The defining equation of `X`." with no formula: `dealerSamples_iff`, `shareStep_eq`, `shareState_eq`, `shareRaw_eq`, `lagStep_eq`, `lagTerm_eq`, `recStep_eq`, `recombineRaw_eq`, `dealerPowStep_eq` and `dealerWord_eq`.<br>• Precedent: BSF-F03. | **LE-h11-doc**, docstrings only: add "Glue." notes and the formula, or "(formula: the body above)" for the long machine bodies. It can be folded into the landing (**EF-H11-R4**). |
| **EFH11-F05** | minor (duplication, cross-job; ledger) | **Two parallel public reindexing lemmas.** `SecretSharing.samplesEfficiently_comap` (reindex an efficient sampler along `φ : P' κ → P κ`) and EF-D1's `LWE.drawSamplable_restrict` (#387; the draw half, along a constant section `s κ`). The latter is a special case of the former's draw half.<br>• Neither is in `CoinSampling/Contract.lean`.<br>• The EF-H11 worker could not see EF-D1, so this is not a disclosure failure. | Ledger row (**EF-H11-R5**). At the EF-D1-W2 promotion window, put `samplesEfficiently_comap` (and a `DrawSamplable.comap`) into `Contract.lean`, and re-derive `drawSamplable_restrict` from it, proof-only. |
| EFH11-I1 | info | **Pre-existing Rule-10 debt in the frozen owners**, found by phase 2 and not caused by EF-H11.<br>• At the check head, coe-A gives `Sharing` 2 failures (`:64` `isSharing_share`, `:147` `recombine_eq_reconstruct`).<br>• `Protocol` has 11 failures: `:94` `isSharing_degreeReduce` (reads `recombine` as its sum), `:131–138` `bgwEval_isSharing` (reads `Circuit.eval`) and `:154–159` `bgwEval_of_isLinear` (reads `Circuit.IsLinear`). `Sharing`'s two read `Shamir.scheme`.<br>• Under the LE variant the same 13 appear, shifted by the 4 inserted lines.<br>• This debt is not recorded in the inventory or the ledger. | Ledger note. LE-h11-w2's `recombine_eq_sum` would also let `isSharing_degreeReduce` be repaired later. |
| EFH11-I2 | info | **Disclosed near-relatives:** `finZModEquiv` (I recommend harvesting one public `Fin p ≃ ZMod p` with both readers, together with `residueFinEquiv`); `invModW` as the first public modular inverse (relative: `DetMod`); and `resWord` against `Encoding/Modular.encodeVector` (a different format). | Ledger note with F05. |
| EFH11-I3 | info | **The gate steps are agreement lemmas** of `addModW`, `mulModW`, `recombineRaw` and `shareRaw` with `bgwEval`'s clauses, not new `∃ f, PolyTimeComputable f ∧ …` bundles per gate. The polynomial-time facts are the leaves' `polyTimeComputable_*`. Input and constant gates are the identity: `resWord_bgwEval_input`/`_const` restate `bgwEval_input`/`_const` under `resWord`, as the brief asked. | Accept. |
| EFH11-I4 | info | **The whole-circuit evaluator is E-SCOPE W3,** under Q-H11-1 (A). The host contract is REPORT §7. | **EF-H11-R6.** |
| EFH11-I5 | info (process) | **Seal variants (the worker's question W4).** The worker had only the gate-04 package; the A/B strict/coe variants of COMMON C6 are the recipe's `mkseals_ab`/`mkseals_coe`, which were not staged. Phase 2's canonical coe-A seal answers W4: the failure set is identical. | Dispatch template: stage the recipe's `seal/review/` tools, or name them, in COMMON C6. |
| EFH11-I6 | info | **C2 (root) was incomplete on the worker's host** (PFR oleans). | Closed in phase 2. |
| EFH11-I7 | info | **Small REPORT discrepancies.**<br>• REPORT says "1,750 insertions"; `git diff --stat` gives 1,761 (1,751 in the new files plus 10 facade lines).<br>• The worker commits carry the worker's own `Claude-Session` trailer. | None. The landing commits carry the required trailers. |
| EFH11-I8 | info | **Size.** 1,761 new lines against the brief's 1,800–3,500 ±40%, with the evaluator (600–1,300) not built. In band. | None. |

## Landing (held)

**Not landed:** F01 is a major. No `land/ef-h11-sharing-bgw` branch was created and no PR was opened.
When Seyoon rules:

1. **Branch.** Create `land/ef-h11-sharing-bgw` from `iO/phase-a-base` (`5ed465f6`), the worker's
   own base, so the picks apply as-is; `git am` already reproduced them there.
   - Make signed `git cherry-pick -S -x` copies of the 6 commits.
   - End every message with:
     ```
     Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
     Claude-Session: https://claude.ai/code/session_01PqpVTiuDcjSqhyfbqnsVxA
     ```
2. **Landing edits, as one signed commit.**
   - **LE-h11-w1** (R1 A).
   - **LE-h11-w2** (R2 A), with the rename and docstring.
   - **LE-h11-doc** (R4 A).
3. **Re-run phase 2 on the landing head:**
   - the replay of `Defs`/`Sharing`/`Protocol` and their downstream (13 modules, as for `a299c19e`);
   - coe-A seals of the 3 new owners, expecting 0;
   - the paired controls;
   - lint, expecting `Defs`/`Sharing`/`Protocol` to change by INFO counts only.
4. **The draft PR,** base `iO/phase-a-base`. Its gate is a Codex gate, to be staged. It lands after
   #374, #378, #384 and #380, or as a stacked PR.
- **Under R1 (B) ("debt now, fix after", the derand precedent):** land the 6 commits as delivered,
  record F01's 4 declarations as named seal debt in the PR body, and follow up with a reader PR.

## Questions for Seyoon (recommended option first)

- **EF-H11-R1 (F01: the `Defs.lean` readers).** How should the four Rule-10 failures be closed?
  - **(A, recommended)** Grant **LE-h11-w1** on the EF-H11 PR. It is the worker's patch, verbatim:
    three `Iff.rfl` readers beside the definitions in `SecretSharing/Defs.lean`, plus the 6-line
    rewrite of the four transfer proofs.
    - Phase 2 shows coe-A at 0 errors with it.
    - `Defs.lean` is in no open PR and not in S2-A's scope.
  - (B) Debt now, fix after (derand precedent): land as delivered, with the 4 named seal failures
    recorded, and add the readers in a follow-up PR.
  - (C) Return the delivery to the worker for an r2 with the same change. The result is the same, and
    it costs a round trip.
- **EF-H11-R2 (F02: the multiplication gate).**
  - **(A, recommended)** Grant **LE-h11-w2** on the same PR:
    - `degreeReduce_apply` in `MPC/BGW/Protocol.lean`;
    - `recombine_eq_sum` (the worker's `recombine_eq`, renamed) in `SecretSharing/Sharing.lean`, both
      `rfl`;
    - `recombineRaw_bgwEval_mul` in `BGW/Efficient.lean`. This closes the gate against `bgwEval_mul`.
  - (B) Grant it with the worker's name, `recombine_eq`.
  - (C) Leave the gate at the recombination step, and add the readers in a later cleanup PR.
- **EF-H11-R3 (F03: interface non-vacuity).**
  - **(A, recommended)** Land as is, and commission a small follow-up statement item:
    - encoding-injectivity fields and `adm_eventually` on `EfficientScheme`;
    - the Shamir proofs, with `shamirEfficient` fixed at an unbounded coin bound.
  - (B) Require it before landing (fill r2).
  - (C) Accept the interface as is, as a convention recorded in its docstring.
- **EF-H11-R4 (F04: docstrings).**
  - **(A, recommended)** Maintainer docstring-only landing edit **LE-h11-doc**: "Glue." notes and
    formulas, folded into the landing.
  - (B) Accept as delivered.
- **EF-H11-R5 (F05, I1, I2: ledger).**
  - **(A, recommended)** Record ledger rows:
    1. Promote `samplesEfficiently_comap` (with a `DrawSamplable.comap`) into
       `CoinSampling/Contract.lean` at the EF-D1-W2 window, and re-derive EF-D1's
       `drawSamplable_restrict` from it.
    2. Harvest one public `Fin p ≃ ZMod p` with readers (`finZModEquiv` with `residueFinEquiv`).
    3. Record the 13 pre-existing Rule-10 failures of `Sharing`/`Protocol` as cleanup debt.
  - (B) Record only the third (the debt). Leave the two near-relatives as they are.
- **EF-H11-R6 (I4: whole-circuit evaluator; the worker's W3).**
  - **(A, recommended)** Commission the circuit encoding and the tree-evaluation host as a statement
    item, following REPORT §7's contract; the evaluator follows in wave 2.
    - **Rule 16:** nothing from Seyoon's machine is needed for it.
  - (B) Record BGW whole-circuit efficiency as out of scope.

## Evidence

`ef-h11-final-r1-evidence.zip` (beside this file; SHA-256 in `evidence-SHA256SUMS`), with an inner
`SHA256SUMS` that does not list itself, and `PROVENANCE.txt`.

| Path | Contents |
|---|---|
| `phase1/` | `integrity.log`, `repro.log`, `hygiene.txt`, `decls2-review.tsv`, the clash-scan inputs (`new-short.txt`, `decl-*.tsv`), `open-prs.txt` |
| `phase2/` | The plans, build records (`results.jsonl`, `permod.tsv`, module logs), state checks, snapshot verifications, probe runs (collector, axioms), seal records and summaries (`rule10*`), seal and control logs, lint outputs, `le-variant.diff` and the scratch hashes |
| `probe-src/` | The axiom and collector probes, the control files (`CtlS_*`, `CtlU_*`), and the generated coe-A seal sources: head, LE variant, and frozen owners |
| `tools/` | `hygiene.py`, `mkctl_efh11.py`, `run-build.sh`. The recipe tools are used unmodified from `olean-rebase-evidence.zip` (`b662b7da…`). |

**Not yet clear to merge — F01 (Rule-10 major) awaits EF-H11-R1; no landing branch or PR yet; the base
stack (#374, #378, #384, #380) is unmerged; the Codex gate is to be staged.**
