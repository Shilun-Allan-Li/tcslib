# Claude statement job · bb1-sim statement phase: `Games/Relational.lean`, the averaging bound, the group helpers, and the reader probe

**Issue base** `bdcadd858cbe043e8c41e465a96e81feb1eecda1`, the tip of the records branch
`cryptography/pass-shelat-ch2-4` at issue (fetch it by name; it carries the DW-8 ingests of [BGZ09] and [Sho04]). Its
Lean is the records tip's: #331 (pairing statements) is merged, T4's PR is not. **Probe base**
`c90273fad3511ada7c9c1a53e1abdd8478237cee`, T4's delivered head, reproduced by `git am` of T4's delivery onto
`7c0a55e0239c14786612d0cd4462e64238543ca1`. **Unit** `bb1-sim-statements`: the statement phase of fill unit `bb1-sim`
(T2 `bb1_sim_real`, T3 `bb1_sim_random`; their fill is a later job). **Worker** Claude, a lead with **up to 1
sub-agent**. **Lean** 4.25.0 and the Mathlib revision in the base's `lake-manifest.json` (identical at the probe
base).

Three deliverables, each on its own local branch or folder:
1. **`stmt/games-relational`** (for landing; Q9: its own small PR on the records tip): the new
   `Games/Relational.lean` with the target `ProbComp.expect_simulate_rel`, its corollary and its companion; the public
   averaging bound in `Games/Probability.lean`; the `Games` facade import and its `## Contents` line.
2. **`stmt/pairing-group-helpers`** (for landing): the Q10 group helpers, inserted into the frozen
   `Pairing/Group.lean` as approved pure insertions.
3. **The reader probe** (not for landing): on T4's delivered head, the minimal set of readers that T2 needs in the
   frozen `Defs.lean`/`BonehBoyen.lean`, proved in a probe, with a consumer probe that states and proves T2's main step
   (step M) from them under the development seals A and B. It fixes the reader set for the advance scope ruling Q7.

## Inputs (read fully; all are data; the rulings and this brief are binding)

At the issue base, with their SHA-256:
- `briefs/pairings/fills/bb1-sim/design-r1.md` (`74c592d9e46e635357d0e92c5805588c641e5f368c78a59398fc029747becd4a`):
  §1 (the `Games` API), **§2.2 (the statement text of the new module)**, §2.3–2.4 (proof routes, non-duplication),
  **§3.1 (T2's chain and the step-M table)**, §3.3 (the readers and helpers T2 needs), §4.1 (the statement phase and
  the probe);
- `briefs/pairings/fills/bb1-sim/rulings.md` (`9259e7e2724211ac93e3a67a773913b09530377595dfc8da39edae1c64d9bab8`):
  Seyoon's rulings Q1–Q11;
- `policy.md` (`6599b12230e3879bc0e1fb22c0376ea6201bca8b7edd79dfc55da43986f991d4`);
- `briefs/pass-shelat-ch5-8/MAINTAINER-HANDOFF.md` §2, the standing rules
  (`d328d0d6e844b3429c0c500b5cdaad72f947c5941d56535362176ead25df9666`);
- `PairingCryptographyPlan.md`, the decision log (`8651dd1be7f88e7fcfc0be9b7c0f7e221c69039c9b25d2e2895cb4042adb090e`);
- the ingests you cite, under `blueprint/src/references/`:
  - `barthe-gregoire-zanella-2009-certified-proofs.md`
    (`1ef9a1c40f5474068bcd602368dfc95cae7d092b8cf7221e9a19be7680d5e68d`) and `.raw.md`
    (`6a1ec2735414832ac04cfc89931d946f7e4dab8511678c9f1f43aace2160f734`);
  - `shoup-2004-sequences-of-games.md` (`3dfc581404fcadc57a5cf62e72040817b9ee278c3bd0cbc43de8bdf0e5bc983f`) and
    `.raw.md` (`9e2635c2529bbc99449e4098984962f1c0f7f67c975ddc1e029fd7eb3ca5921c`);
- the ingest review `briefs/pass-shelat-ch5-8/ingests/dw8-final-r1/review.md` §4, the citation strings
  (`c7c3a24c5342ba71ed757ba71f48a59b30a11ae4b27969570060200cb0e2c8a6`).

On `exchange/pass-shelat-ch5-8`, for the probe:
- T4's delivery `inbox/fills/bb1-machine/` (final commit "fill bb1-machine: final",
  `f14ac810da888829d21a1bd94fef4dcd4258b863`): `REPORT.md`, `patches/` (three patches and `COMMITS.tsv`),
  `src/`, `evidence/build/order-final.txt` (SHA-256 `f17ade1ee12c9d11a03d0409dc4553b7d0743997a4077cca614cc902ed477c3c`,
  189 modules), and `evidence/tools/` (the adapted seal, control, scan and build tools). Verify the delivery with its
  top-level `SHA256SUMS`;
- T4's issued pack `outbox/fills/bb1-machine/`: `brief.md` (the seven readers, the Rule 10 discipline) and
  `checkpoint/tools/` (`dev/devseal.py`, `devcheck.sh`: the development seals the in-house T4 probe used).

**What changed since the design note.** The design's §2.2 text is the basis of `Relational.lean`, with these
supersessions:
- **Citations (Q11).** The ingests have landed. Cite [BGZ09] and [Sho04] directly, with the strings of *Sources and
  citations* below. The design's "⟨location to pin⟩" placeholders and its description of [BGZ09] as having a "rule
  for adversary calls" are **superseded**: [BGZ09] states no such rule (review F4).
- **Averaging bound (Q6).** It goes into `Games/Probability.lean`, not `Relational.lean`.
- **Group helpers (Q10).** They go into `Pairing/Group.lean`, not into a fill helper module.

## Binding rulings (Seyoon, 2026-11-16; full text in `rulings.md`)

- **Q1.** A new module `Games/Relational.lean`, imported by the `Games` facade.
- **Q2.** Names `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel`, `expect_sample_rel`, beside
  `ProbComp.expect_simulate_congr`.
- **Q3.** The inline expectation form of the per-call hypothesis (design §2.2).
- **Q4.** The companions `prob_simulate_rel` and `expect_sample_rel` are part of the statement phase.
- **Q5.** No query budget.
- **Q6.** The averaging bound `|𝔼 f − 𝔼 g| ≤ 𝔼 h` becomes a public lemma in `Games/Probability.lean`, beside
  `ProbComp.abs_expect_sub_le`. The private ETT copy (`Encryption/PrivateKey/EncryptThenTag/Forgery.lean:515`) is
  re-pointed later, in the DW-4 / DL-40 cleanup: **do not touch `Forgery.lean`**.
- **Q7.** One reader `IBEScheme.sidImpl_eq_oracleImpl`, a pure insertion in `Defs.lean` after T4's `_onSpec` readers,
  carried by the bb1-sim PR under an advance scope ruling **confirmed by a probe first**; the probe also fixes any
  needed `encCT` reader. This job is that probe. It does not edit `Defs.lean` or `BonehBoyen.lean` on any branch.
- **Q8.** One bb1-sim gate after Gate 44 audits this statement phase, the reader insertions and the fill.
- **Q9.** The Games statement phase is its own small PR on the records tip.
- **Q10.** The group helpers go into the frozen `Pairing/Group.lean` as approved insertions beside the `G_T` bijection
  `pow_val_bijective`: `Z_p ≃ G` for `g ≠ 1`, the additive exponent laws in `G`, and identity injectivity on good coins.
  Reuse Mathlib's `orderOf`/`ZMod` API where it applies.
- **Q11.** Cite [BGZ09] and [Sho04] for the relational simulation lemma (now ingested; see *Sources and citations*).

## Feasibility and size (maintainer's assessment)

Feasible in one session. Branch 1 is about **160–200 lines** in the new module (three statements, two `sorry`d with
sketches, one proved in three lines), about **15 lines** in `Probability.lean` (a seven-line proof moved from the ETT
copy) and **4 lines** in the facade. Branch 2 is about **40–70 lines** of short proved helpers. The probe is the
largest piece of Lean, about **300–600 lines** outside the library, all `rfl`-style readings and structural
comparisons; group algebra may enter it as hypotheses. The long steps are mechanical: the bootstrap of the 612-module
order, the sweep of `Probability.lean`'s 150 downstream modules, and the probe's own 189-module tree.

## Branches, series and delivery

- **Checkout.** In your own clone, fetch `cryptography/pass-shelat-ch2-4` by name, check that its tip or an ancestor is
  the issue base, and start at the exact issue base (`git rev-parse HEAD`; record it in `REPORT.md`). If the branch has
  moved on, **stay on the issue base**; the maintainer rebases at landing.
- **Series 1, `stmt/games-relational`** (from the issue base): suggested commits, each compiling:
  1. `stmt games-relational: public averaging bound in Games/Probability (Q6)`;
  2. `stmt games-relational: Games/Relational, the relational simulation statements (Q1-Q4)` (with the facade).
- **Series 2, `stmt/pairing-group-helpers`** (from the issue base, independent of series 1): one commit,
  `stmt pairing-group-helpers: group helpers in Pairing/Group (Q10)`.
- **The probe** (not for landing): in a separate worktree, fetch `fill/pairings-bb1-machine` (tip
  `7c0a55e0239c14786612d0cd4462e64238543ca1`), start a local branch `probe/bb1-sim-readers` there, and apply T4's
  delivered patches as T4's `REPORT.md` describes (`git am` of `inbox/fills/bb1-machine/patches/*.patch`, with the
  author and committer data of `patches/COMMITS.tsv`). Check `git rev-parse HEAD` =
  `c90273fad3511ada7c9c1a53e1abdd8478237cee` and record it. The probe files live **outside `TCSlib/`** (for example
  `PlProbe/`). They may be committed on `probe/bb1-sim-readers`, which is never delivered as a patch series and never
  pushed.
- Keep every branch local. Commit series 1 and 2 with `git -c commit.gpgsign=false`. The maintainer opens the PRs
  after review; Seyoon approves and merges.
- **Deliver** every checkpoint and the final only under `inbox/fills/bb1-sim-statements/` on
  `exchange/pass-shelat-ch5-8`:
  - `REPORT.md` (*Report*);
  - `patches/games-relational/` (`git format-patch <base>..stmt/games-relational`) and `patches/group-helpers/`
    (`git format-patch <base>..stmt/pairing-group-helpers`), each with a `COMMITS.tsv`: one row per commit with its
    hash, the author's name, email and date, the committer's name, email and date, and its **signing** (`none`, or the
    format), so that `git am` at the base reproduces every hash. Check the reproduction of both series in a scratch
    clone before you push, and say so in `REPORT.md`;
  - `src/games-relational/` and `src/group-helpers/`: every new or changed file at that branch's head, under its
    repository path;
  - `probe/`: the probe sources as `.lean.txt`, the sealed variants as checked, and `probe/READERS-TO-INSERT.md` (*The
    probe*);
  - `evidence/`, with its manifest `evidence/SHA256SUMS` (*Evidence completeness*);
  - a top-level `SHA256SUMS` listing every delivered file except itself. The delivered paths must **equal** the
    manifests' paths: nothing missing, nothing extra, no leading `./`. Check this before each push.
- Commit on the exchange as `stmt bb1-sim: checkpoint N` and `stmt bb1-sim: final`. Pull with rebase before pushing;
  push only your path; never force-push; never touch another path (other fills, gates, `arora-barak-ch3-4/`,
  `lwe-sis-constructions/`, T4's `inbox/fills/bb1-machine/`). Never push a campaign branch. If a push is refused, keep
  the commit and say so.

## Base and parallel work

- **T4's PR** (`fill/pairings-bb1-machine` plus the delivered series, Gate 44) is open and not on the issue base. Series
  1 and 2 do not depend on it and touch none of its files (`Defs.lean`, `BonehBoyen.lean`, `BonehBoyenMachine*`).
- **Series 1** touches only `Games/`. **Series 2** touches only `Pairing/Group.lean`. They are path-disjoint from
  each other and from T4's PR. Series 2's downstream closure contains T4's files (`BonehBoyen`, `BonehBoyenMachine`),
  which it rebuilds but does not edit.
- **T1** (`bdhAssumption_of_dbdhAssumption`, #340) is still `sorry` at the base. Nothing here uses it.
- **Nothing of the fill.** T2 and T3 stay `sorry`; `BonehBoyenSecurity.lean` is frozen; no lazy handler, no helper
  module under `IdentityBased/`.

## Scope

**Series 1 may change exactly:**

| File | Permitted change |
|---|---|
| `TCSlib/Cryptography/Games/Relational.lean` | **new**: the module of design §2.2, amended as *Deliverable 1* says |
| `TCSlib/Cryptography/Games/Probability.lean` (409 lines, SHA-256 `a7d79d12d14ae90d88b7eec368afa8f311eb30864ee8c9b9b72f9f75548dee32`) | two pure insertions: the lemma after line 403 (the last line of `abs_expect_sub_le`, `  constructor <;> linarith`), before `end Sampling` (line 405); one `## Main results` bullet after line 48 |
| `TCSlib/Cryptography/Games.lean` (64 lines, SHA-256 `dd67d6952d872a95cc03e34f477dace41bcfb96d50a79daa383064a7d64f2693`) | two pure insertions: `import TCSlib.Cryptography.Games.Relational` after line 9 (`…Games.Hopping`); one `## Contents` entry after line 42 (the end of the `Hopping` entry) |

**Series 2 may change exactly:**

| File | Permitted change |
|---|---|
| `TCSlib/Cryptography/Pairing/Group.lean` (304 lines, SHA-256 `ae72aa9cdda09be12eca8a7512b0cecb00074ce69cef6e1ce0bef1e3dfc8ce9d`) | two pure insertions: the helper block after line 232 (the last line of `pow_val_bijective`), before `end BilinearGroup` (line 234); its `## Main results` bullets after line 62 (the `pow_val_bijective` bullet). **No new import.** |

**Frozen:** everything else, including `Games/Hopping.lean`, `Games/Simulate.lean`, `TCSlib.lean`, every file under
`IdentityBased/`, `EncryptThenTag/Forgery.lean` and `blueprint/`. On the probe branch, `Defs.lean` and
`BonehBoyen.lean` are frozen too: the readers are proved **in the probe**, not inserted.
- **Scope requests.** If a statement or helper needs any other change to a frozen file (an import, a reader, a moved
  declaration), stop that line of work and ask Seyoon in your session with the file, the diff and the reason; proceed
  only on his approval, and record the request and answer verbatim under `evidence/scope-request/` and in `REPORT.md`.
  Seyoon prefers routes with no frozen-file edit.

## Deliverable 1: `stmt/games-relational`

### 1a. The averaging bound in `Games/Probability.lean` (proved)

Insert, after line 403 and one blank line, inside `namespace ProbComp` / `section Sampling` (the file's `variable
{α β : Type}` applies):

```lean
/-- **Averaging a pointwise bound:** expectations of functions within a pointwise bound of each
other are within the expectation of the bound:
`(∀ x, |f x - g x| ≤ h x) → |𝔼_c f - 𝔼_c g| ≤ 𝔼_c h`. -/
theorem abs_expect_sub_le_expect (c : ProbComp α) {f g h : α → ℝ}
    (hb : ∀ x, |f x - g x| ≤ h x) : |expect c f - expect c g| ≤ expect c h := by
  rw [← expect_sub, abs_le]
  constructor
  · have := expect_mono c fun x => (neg_le_of_abs_le (hb x))
    rw [show (fun x => -h x) = fun x => (-1) * h x from funext fun x => by ring,
      expect_const_mul] at this
    linarith
  · exact expect_mono c fun x => le_of_abs_le (hb x)
```

- The statement is the private ETT copy's (`Forgery.lean:515`) with `α` for `β`; the proof is its proof. If it does
  not elaborate as given, repair the proof only, inside this file (the owner reads its own definitions), and say so.
- Bullet after line 48: `* \`ProbComp.abs_expect_sub_le_expect\`: averaging a pointwise bound.` (wrap to 100).
- **The name** is the ETT copy's short name, so that the DL-40 re-point is a deletion. `Forgery.lean` declares its
  copy `private` in `namespace …Composability.ETTGame` and opens `…Games ProbComp`; Lean resolves the current
  namespace first, so the call at `Forgery.lean:545` should stay unambiguous. **The downstream sweep is the check**:
  `Forgery.lean` is in it. If it reports an ambiguity, rename the new lemma to `abs_expect_sub_le_of_abs_sub_le`,
  record the failing log, and say so; never edit `Forgery.lean`.

### 1b. `Games/Relational.lean`

Write design §2.2's module (namespace `TCSlib.Cryptography.Games`, `ProbComp` inside), with these rules:
- **Headers verbatim.** The three declarations' headers (keyword, name, binders, type, up to `:= by`) are design
  §2.2's text exactly. If one does not elaborate, make the smallest change that does, never weaken it (no added
  hypothesis, no narrower type), and list it in `REPORT.md` § *Statement changes against design r1* with the error.
- **Bodies.** `expect_simulate_rel` and `expect_sample_rel` are `sorry`. `prob_simulate_rel` is **proved** from
  `expect_simulate_rel` (design §2.2: `classical`, `prob_eq_expect` twice, then `expect_simulate_rel … (fun _ _ _ _
  => rfl)`; repair the proof if needed). Do not prove the two targets: they are the fill's.
- **Imports.** Only `TCSlib.Cryptography.Games.Simulate` and `TCSlib.Cryptography.Games.Probability`.
- **Docstrings.** Each declaration: a formula docstring (design §2.2's prose) and a `**Proof sketch.**` (design §2.2
  and §2.3: the induction outline for L1, the reindexing for L3). Replace every citation placeholder as *Sources and
  citations* says; the `**Deviation:**` paragraph of `expect_simulate_rel` becomes the F4 note given there. The module
  docstring keeps design §2.2's sections (`## Main definitions`: None; `## Main results`; `## References`) with the
  References lines given there.
- No `@[simp]`, no attribute, no definition (so no reader is owed), no `open` beyond what the statements need.
- **Facade.** In `Games.lean`: the import after line 9, and after line 42 the entry
  `* \`TCSlib.Cryptography.Games.Relational\`: simulations of two implementations on related states (the relational
  form of simulation congruence).` wrapped to 100 in the facade's style. The facade lint requires the import (a facade
  must import each child; without it the lint gains a FAIL line).

## Deliverable 2: `stmt/pairing-group-helpers`

Insert into `namespace BilinearGroup` (its `variable {wG wT : ℕ} (B : BilinearGroup wG wT)` applies), after line 232
and one blank line, the helpers of Q10, each with a formula docstring, proved (all are short):

| Helper (suggested name) | Statement |
|---|---|
| `BilinearGroup.pow_val_add` | `(x : B.G) (a b : ZMod B.order) : x ^ (a + b).val = x ^ a.val * x ^ b.val` |
| `BilinearGroup.pow_val_neg` | `(x : B.G) (a : ZMod B.order) : x ^ (-a).val = (x ^ a.val)⁻¹` |
| `BilinearGroup.pow_val_bijective_of_ne_one` | `{g : B.G} (hg : g ≠ 1) : Function.Bijective fun a : ZMod B.order => g ^ a.val` (the `Z_p ≃ G` of design §3.3; the fill builds the `Equiv` by `Equiv.ofBijective`, so no new definition and no reader) |
| `BilinearGroup.natCast_inj_of_lt` | `{m n : ℕ} (hm : m < B.order) (hn : n < B.order) : (m : ZMod B.order) = n ↔ m = n` (identity injectivity on good coins) |

- **Why the last one is generic.** `bitsToNat`, `bitsToNat_lt` and `bitsToNat_injective` live in
  `Asymptotic/Sampling.lean`, which is **not** upstream of `Group.lean` (checked at the base), and Q10 approves
  insertions, not imports. So the helper is stated for naturals below the order; the fill composes it with
  `bitsToNat_lt` and `2^ℓ ≤ p` to get `idToZ ID ≠ idToZ ID*`. If you judge the `bitsToNat` form necessary in
  `Group.lean`, that needs an import: a scope request, not a change.
- **Mathlib first (Q10, standing rule 13).** Before inserting each helper, search Mathlib (`exact?`/`apply?` on the
  statement in a scratch probe, and name searches such as `ZMod.val_add`, `ZMod.val_natCast_of_lt`,
  `ZMod.natCast_eq_natCast_iff'`, `pow_eq_pow_iff_modEq`, `orderOf_eq_prime`, `zpow_mod_orderOf`). If Mathlib states
  a helper for any finite group or for `ZMod` already, in a form the fill can use directly, **do not insert it**: list
  the Mathlib lemma in `REPORT.md` instead. The proofs follow the file's own patterns (`pow_val_mul`: `ZMod.val_add`,
  `Nat.mod_add_div`, `pow_order`; `pow_val_bijective`: `orderOf_eq_prime`, `pow_eq_pow_iff_modEq`,
  `Fintype.bijective_iff_injective_and_card`, `card_G`).
- Names are suggestions: choose clash-free descriptive names (*Checks* 11) and record them. Add any further exponent
  law only if design §3.1's steps need it (for example a `_GT` form for the challenge row), and say which step uses it.
- `## Main results` bullets after line 62, one per inserted helper, in the file's style.
- No tag is required (technical glue, policy §2); `pow_val_mul` carries none.

## Deliverable 3: the probe (Q7's advance scope evidence; not for landing)

**Goal.** Fix the minimal set of readers that T2 needs in the frozen `IdentityBased/Defs.lean` and
`IdentityBased/BonehBoyen.lean`, beyond T4's seven, by proving T2's main step from them under the development seals.

**Files** (outside `TCSlib/`, in the probe worktree at `c90273fa…`):
1. **`PlProbe/BB1SimReaders.lean`, the candidate readers**, proved owner-side (`rfl` or one line, as an owner would),
   built natively through `scripts/lean_check_tree.sh` into the probe's olean tree. It stands in for the two owners: it
   is **not** sealed. Start from:
   - `IBEScheme.sidImpl_eq_oracleImpl` (design §3.3): `S.sidImpl b κ pp msk = S.oracleImpl κ (S.sidImpl b κ pp msk 0)
     (S.sidImpl b κ pp msk 1) (S.sidImpl b κ pp msk 2)` (`funext` and a three-way `match` with `rfl`); if the
     whole-function form is awkward to rewrite with, the pointwise form `… i x s = S.oracleImpl … i x s`;
   - an `encCT` reader **only if needed**: `ofFn_bb1Scheme_encCT`, the word form of `(bb1Scheme G ℓ).encCT κ ⟨d, c⟩`
     parallel to T4's `ofFn_bb1Scheme_encSK`. First try without it: the real challenge is
     `encCT κ ⟨pp.1, BB1.encrypt …⟩` (`bb1Scheme_enc`) and the simulated one `encCT κ ⟨d, ⟨…⟩⟩` (`bb1SimCt_eq`), so
     equal ciphertext structures may compare by `congrArg` with no word reader.
   - The alternative of ruling Q7(B), three readers `sidImpl_{zero,one,two}_onSpec` in T4's `_onSpec` form, only if
     `sidImpl_eq_oracleImpl` fails: record why.
   - **Constructing values.** T4 found that anonymous constructors `⟨d, pp⟩ : (bb1Scheme G ℓ).PP κ` do not elaborate in
     a consumer under the seals. Obtain parameters and keys from the setup's output (`bb1Scheme_setup`,
     `BB1.setup_eq`) or along the published type equation `bb1Scheme_PP`, never by unfolding. A further reader is a
     last resort, and is reported as such.
2. **`PlProbe/BB1SimStepM.lean`, the consumer probe**, importing the readers probe, `BonehBoyen` (and
   `BonehBoyenSecurity` if you state T2), and only modules of T4's order. It contains no `sorry`, `admit`, `axiom` or
   `native_decide`. It states and proves:
   - **P-1, reading `sidImpl` at the game's query type** (any `S : IBEScheme`): for each of the nine cases of
     `Defs.lean`'s typed readers (`sidImpl_init_none`/`_some`, `_keyGen_none`/`_target`/`_ne`,
     `_challenge_none`/`_repeat`/`_fresh`/`_invalid`), the call `S.sidImpl b κ pp msk i x s` with
     `x : (S.sidSpec κ).dom i`, equal to the typed reader's right side with the casts of `oracleImpl_*_onSpec`. Proved
     from the candidate readers, `oracleImpl_*_onSpec` and the typed readers; type equations of casts only from
     `sidSpec_eq`, `bitSpec_dom`/`_rng`, `inLens_*`, `outLens_*` (type-level Rule 10).
   - **P-2, step M of design §3.1** (`S = bb1Scheme G ℓ`): for each row of the step-M table, the comparison of the real
     handler `S.sidImpl b κ pp msk` (parameters `(g, X, Y, h)` from the setup's output shape) with
     `bb1SimImpl b κ d g X Y (g^c) (e(g,g)^{αb'c})` from related states, in the pointwise form the fill will feed to
     `expect_simulate_rel`: deterministic rows as equal `pure` answers with related states; sampling rows (`Init`
     uncommitted with `h = X^{(−ID).val} g^{α₁.val}` as a function of `α₁`; `KeyGen` for `ID ≠ ID*` with
     `r̃ ↦ r̃ + b'/(ID − ID*)`; the first valid `Challenge` with `s = c`) as the premise `hf` of `expect_sample_rel`:
     each call read as `(sample U).bind fun u => .pure (f u)`, with equal answers and related new states along the
     bijection. The relation is design §3.1's `R`. The real side is read through P-1 and T4's readers, the simulator
     side through `bb1SimImpl_eq`, `oracleImpl_*_onSpec` and the `bb1Sim*` readers.
   - **Group algebra** may enter P-2 as explicit hypotheses of the probe lemmas: equations in `B.G`, `B.GT` or
     `ZMod B.order` that mention no IBE definition (for example `F(ID*) = g^{α₁}`, BB04's key identity, the exponent
     laws of deliverable 2). List each in `READERS-TO-INSERT.md`. The probe tests the **reading**, not the algebra.
   - **P-3, T3's challenge row** (expected, cheap): `bb1SimImpl` with `T` against `T'` at the first valid challenge,
     along `T ↦ decodeT M₁⁻¹ · decodeT M₀ · T`, to confirm that T3 needs no reader beyond T4's.
   - **Minimum** if time runs short: P-1, and the P-2 rows `Init` uncommitted, `KeyGen` for `ID ≠ ID*`, the first valid
     `Challenge` and the invalid `Challenge` (the rows that touch `encPP`, `encSK`, `encCT` and `MsgSpace`). Name every
     row not done.
3. **Checks.** The readers probe: native, rc 0, 0 errors. The consumer probe: natively and under the **development
   seals A and B** (`devseal.py` from T4's `checkpoint/tools/dev/`, paths adapted: every imported TCSlib definition
   locally irreducible, `PolyExpr.eval` open in A), each rc 0 with 0 errors in both forms; the sealed counts
   ("DEVSEAL A sealed N") recorded; `#print axioms` of every probe lemma: `propext`, `Classical.choice`, `Quot.sound`
   only. This is not the canonical seal: the canonical seals run on the owners once the readers land (the fill and
   the bb1-sim gate).
4. **`probe/READERS-TO-INSERT.md`**, the scope evidence for Seyoon:
   - the **minimal** reader set: each reader with its exact Lean text (formula docstring, at most 100 characters per
     line, ready for a byte-for-byte insertion), its owner, its insertion anchor in T4's delivered files (`Defs.lean`
     at T4's head: after line 430, the last line of `oracleImpl_two_onSpec`, before the `sidCodec` docstring;
     `BonehBoyen.lean` at T4's head: after line 412, the last line of `bb1Scheme_msgSpace_iff`, before the
     `bb1_correct` docstring), and the probe lemmas that use it;
   - every candidate dropped, with the reason (for example "`ofFn_bb1Scheme_encCT`: not needed; the challenge rows
     compare by `congrArg` through `bb1SimCt_eq`");
   - the alternatives tried and failed, with their logs;
   - the algebraic hypotheses of P-2, each mapped to its intended provider (a deliverable-2 helper, Mathlib, or the
     fill);
   - the rows not done, if any.

   A reader that no probe lemma uses is not in the set. The reader names must clash with nothing at the issue base or
   at T4's head (*Checks* 11).

## Multi-agent work (ruling: up to 1 sub-agent)

- **The lead owns the job:** the brief, series 1 and 2, every commit, the integration, the seals, the delivery and
  `REPORT.md`. Only the lead commits on `stmt/games-relational` and `stmt/pairing-group-helpers`, runs `lake`, fetches
  the cache, and pushes.
- **Suggested split:** the lead does series 2, then series 1, and the evidence; the sub-agent does the probe in its own
  worktree at T4's head, with its own TCSlib olean tree (the probe tree of the addendum's adaptation) and
  `.lake/packages` linked to the lead's. Another disjoint split is fine if recorded; a file is reassigned only through
  the lead, after its owner has stopped.
- **One Lean process at a time on the host**, for both agents, through one lock (for example
  `flock <clone>/.lean.lock …`), released between modules.
- Sub-agent logs go under `evidence/subagents/<name>/`; `REPORT.md` records who wrote what.

## Checks and evidence

Run Python as `python3 -I`. Never run `lake build` or an unfiltered `lake exe cache get`; check one module at a time
with `scripts/lean_check_tree.sh` (the addendum). Count errors in both forms (`^\S+\.lean:\d+:\d+: error[:(]`) in every
log, and keep every raw log. Tools: adapt T4's delivered `evidence/tools/` (exchange, `inbox/fills/bb1-machine/`):
`review/runner.py`, `seal/runner_full.py`, `seal/rule10_b.sh`, `seal/review/{mkcollect,mkseals_ab,mkseals_coe,
ctlcheck2,sealsum,touched}.py` with `archived-gate10-tools/`, `seal/scan1_g40.py`, `seal/scan2.py`, `seal/decls2.py`,
`widths.py`, `sweepsum.py`. Copy what you use into `evidence/tools/`, change the host paths, and record each change in
the tool's header.

1. **Bootstrap and builds** (series 1 and 2, the base tree).
   - Bootstrap `order.txt` (612 modules; the upstream closure of every module downstream of `Probability.lean` or
     `Group.lean`, root excluded) at the issue base: rc 0, 0 errors, and the `sorry` warnings of `base-sorries.txt`.
   - **Series 2 head:** check `Group.lean` and every module of `closures.txt`'s `DOWN-GROUP` except the root (11
     modules, among them `BonehBoyen`, `BonehBoyenMachine`, `BonehBoyenSecurity` and the facades).
   - **Series 1 head:** check `Relational.lean` (inserted into your order after `Games/Simulate`), `Probability.lean`
     and every module of `DOWN-PROBABILITY` except the root (150 modules, `Forgery.lean` and the `Games` facade among
     them).
   - Before each sweep, rebuild every module whose source at that head differs from the source its olean was built
     from, then everything downstream of it; bind every checked source to `git show HEAD`
     (`evidence/build/<branch>/summary.txt`: module, rc, errors in both forms, `sorry` warnings, source hash).
   - **The root** `TCSlib` (1,351 modules at the base) is outside the narrowed bootstrap: do not build it. The facade
     `Games.lean`, its only new consumer edge, is in the sweep; the name-clash scan covers the root's risk; the
     maintainer builds the root at landing, as for every fill of this campaign.
2. **Admissions.** At the series 1 head: exactly `base-sorries.txt` (28 declarations in 14 modules) plus
   `expect_simulate_rel` and `expect_sample_rel` in `Games/Relational` (30 in 15). At the series 2 head: exactly
   `base-sorries.txt` (unless a helper is a target, which this brief does not expect).
3. **Statements.** `python3 -I briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py . <base> <files…>` over each
   series' new and changed files: series 1 ADDED exactly the three `Relational` declarations and
   `abs_expect_sub_le_expect`, series 2 ADDED exactly the inserted helpers; 0 CHANGED, 0 REMOVED in both. A `StmtDump`
   probe prints every new constant with its full name and type. The three `Relational` headers against design §2.2:
   a `python3 -I` check, PASS or each difference listed under *Statement changes against design r1*.
4. **Axioms.** `#print axioms` of every new constant. Expected: `abs_expect_sub_le_expect` and the helpers
   `propext`, `Classical.choice`, `Quot.sound` only (or a subset); `sorryAx` in exactly `expect_simulate_rel`,
   `expect_sample_rel` and `prob_simulate_rel`. A **dependency trace** names, for each constant reaching `sorryAx`,
   the targets through which it does (`prob_simulate_rel` through `expect_simulate_rel` only).
5. **Insertion checks** (`Probability.lean`, `Games.lean`, `Group.lean`), a `python3 -I` script under
   `evidence/headers/`: removing the inserted blocks restores the base byte for byte; each block is at its anchor;
   final hashes recorded. Controls, each giving the stated result: one character changed in a base line: FAIL, exactly
   one difference; one base line deleted: FAIL, exactly one removal; one extra line elsewhere: FAIL; a block moved:
   FAIL.
6. **Rule 10.** Readers only for other files' definitions (policy §1; core and Mathlib definitions may reduce in a
   `rfl`, `decide` or `show` step but are never passed to `simp`, `rw` or `unfold`). Each owner reads its own
   definitions directly.
   - **Canonical seals** A and B, strict and coe (the coe-variant seal A canonical), with `-DmaxErrors=0`, over the
     full TCSlib import closure, of every new or changed owner: `Relational` and `Probability` at the series 1 head,
     `Group` at the series 2 head; and **base seals** of `Probability` and `Group` at the issue base. Report each seal's
     request count and every failing declaration, and attribute every difference from the base by its raw log (new
     theorems add no request). The facade `Games.lean` declares nothing: no seal, and the report says so.
   - **Paired controls** on each new or changed owner that defines something: `Probability` (a negative that reads
     `ProbComp.expect` or `prob` from another file by `rfl`/`unfold`, a positive through `expect_pure`/`prob_eq_expect`)
     and `Group` (a negative reading `BilinearGen.inst` or `desc` by `rfl`, a positive through `inst_eq`/`desc_eq`).
     Each sealed negative fails exactly once, each positive passes, all pass unsealed (pretest first); strict and coe
     both `ALL_OK True`. `Relational` defines nothing: no pair, and the report says so.
   - **The explicit-unfold scan** over the changed files: 0 foreign.
   - **Notation, never sealed:** reducible abbreviations (`QueryImpl`, `ProbComp`, `IBEScheme.sidSpec`, `SidState`,
     `BB1SimState`), `PolyExpr.eval`, projection coercions.
   - The probe's development seals are *Deliverable 3*'s check, not a canonical seal.
7. **Frozen-file check.** No file outside the scope tables changed on either series (`git diff --stat` against the
   base, and the insertion check above).
8. **Lint.** `python3 -I scripts/style_lint.py <new and changed Lean files>`: 0 findings.
   `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b` at the base and at both heads; the
   maintainer's baseline at the issue base is **92 FAIL / 103 WARN over 450 files**. Diff the line sets: no new FAIL
   line, and no new WARN line except one you disclose and justify. Also `dev/sk15.py` (T4's tools) on the new code.
9. **Sizes and widths.** Lines and maximum width of every new and changed file and of the probe files, at each head:
   every line at most 100 characters, every file at most 1000 lines.
10. **Sketches.** Every `sorry`'d target and every proof of 15 lines or more carries a `**Proof sketch.**`.
11. **Name-clash scan.** No new name, public or private (namespaces resolved), is already declared in `TCSlib/` or
    `audits/` at the issue base; the probe's reader names also at T4's head. Report same-short-name hits:
    `abs_expect_sub_le_expect` has one, the private ETT copy (disclose it; it is Q6's intended re-point).
12. **Reuse and overlap** (`REPORT.md` § *Overlap and reuse*). Search first (policy duplication rule; undisclosed
    copies of public lemmas are majors). Carry design §2.4's table (confirm or correct each row), add the private ETT
    copy for `abs_expect_sub_le_expect`, and for each group helper its nearest relatives (`pow_val_mul`,
    `pow_val_bijective`, Mathlib). List the searches you ran.

**Checkpoints** (at least one mid-way): checkpoint 1 is the probe complete (*Deliverable 3* with its checks and
`READERS-TO-INSERT.md`), and series 2 if it is done; the final has everything. Send checkpoint 1 as soon as the probe is
complete: it feeds Seyoon's scope ruling.

## Sources and citations

Use exactly these strings (review §4); the anchors are for checking against the ingests at the base, and are not part
of the string. **Never fabricate** a quotation, location or anchor.

| Use | Citation string | Anchor |
|---|---|---|
| conclusion form: related runs, test functions agreeing along the relation, equal expectations | `[BGZ09, §4.1, lemma (=⟦⟧)]` | `pdf-216f8cd86ce5-p007-b005` |
| the invariant carried as pre- and postcondition | `[BGZ09, §4.2, ⊨_φ]` | `pdf-216f8cd86ce5-p008-b003` |
| pRHL judgment semantics | `[BGZ09, §4.1, Def. 5]` | `pdf-216f8cd86ce5-p007-b002` |
| equivalence inside an arbitrary context, oracle replacement | `[BGZ09, §5.2, Lemma 1]` | `pdf-216f8cd86ce5-p009-b002` (and `p009-b003`/`p010-b001`) |
| adversaries may call oracles only | `[BGZ09, §3.4]` | `pdf-216f8cd86ce5-p006-b001` |
| bridging step: purely conceptual change, `Pr[S_i] = Pr[S_{i+1}]` | `[Sho04, §1.1, bridging steps]` | `pdf-fde1f65e83ec-p003-b002` |
| worked bridging step: random function against a lazily tabulating oracle | `[Sho04, §4.2, Game 2]` | `pdf-fde1f65e83ec-p013-b001` |

- **`expect_simulate_rel`:** at least `[BGZ09, §4.1, lemma (=⟦⟧)]`, `[BGZ09, §4.2, ⊨_φ]` and
  `[BGZ09, §5.2, Lemma 1]`; `[BGZ09, §4.1, Def. 5]`, `[BGZ09, §3.4]` and the two [Sho04] strings where the prose uses
  them. Its `**Deviation:**` paragraph is the **required F4 note**, verbatim: "[BGZ09] states no rule for adversary
  calls with a relational invariant. This lemma generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations
  whose states are related by an invariant, in the arbitrary-context style of §5.2." You may add one sentence that the
  per-call hypothesis (equal expectations of test functions agreeing along `R`) is the library's formulation. **Never**
  write `[BGZ09, rule …]` or describe an "adversary rule" of [BGZ09].
- **`prob_simulate_rel`:** `[Sho04, §1.1, bridging steps]`.
- **`expect_sample_rel`:** no tag (framework glue, policy §2), or `[BGZ09, §4.1, Def. 5]` if the docstring says that
  the bijection witnesses the judgment.
- **Module `## References`** of `Relational.lean`, verbatim:
  ```
  * [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
    Cryptographic Proofs*, POPL 2009.
  * [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
    Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
  ```
- `abs_expect_sub_le_expect` and the group helpers carry no tag. Do not add reference files, edit `blueprint/` or run
  `scripts/sources.py`. Identifiers use the Greek `μ` (U+03BC), never the micro sign.

## Report

`REPORT.md` gives: the base, both heads and the probe head; who wrote what; the changed files with lines at base and
head; the new declarations; § *Statement changes against design r1* (none, or each); the Mathlib reuse decisions for
the helpers; the builds and admissions (checks 1–2); statements, axioms and the dependency trace (3–4); the insertion
and frozen checks (5, 7); Rule 10 seals, base seals, controls and scan (6); lint, sizes and sketches (8–10); the clash
scan (11); § *Overlap and reuse* (12); **the probe** (its checks and a summary of `READERS-TO-INSERT.md`); § *Scope
requests* (none, or each with Seyoon's answer); questions for Seyoon, if any; the evidence, with its manifest.

### Evidence completeness

Every file that `evidence/SHA256SUMS` names is delivered: seal and control sources, manifests and request records, the
insertion and header checks with their outputs and controls, the clash scan, the dependency trace, the probe logs and
sealed variants, every raw log and `results.jsonl`, the sub-agent's logs, and the tools used. If the evidence is too
large for one commit, deliver it in several commits or numbered ZIP parts, each with an entry list; leave nothing out
for size. Check before each push that the delivered paths are exactly the manifests' (top level and `evidence/`), with
no leading `./`.

## Blockers: stop and report

- **E-RES (environment).** The addendum's preflight or cache rules fail. Stop and report the numbers.
- **E-SCOPE (frozen files).** A statement or helper needs a change outside the scope tables (an import, a reader, a
  frozen declaration), or the probe needs a reader beyond the candidates. For series 1 and 2: stop that line and ask
  Seyoon in your session (*Scope*). For the probe: add the reader to the readers probe and report it in
  `READERS-TO-INSERT.md`; that is the probe's purpose, not a blocker, unless it needs a change to a definition.
- **E-ROUTE (statements).** A design §2.2 header does not elaborate even after the smallest repair, or looks false
  (the probe or a `StmtDump` shows it). Do not weaken it silently: keep the design's form out of the branch, and put
  the counterexample or error and your proposed statement in `REPORT.md` as a question for Seyoon.
- **How to report.** Push a checkpoint `stmt bb1-sim: checkpoint N (blocked: <code>)` whose `REPORT.md` opens with the
  blocker, the exact obligation or request, and the logs. Keep everything that already passes.

**Ready to dispatch**
