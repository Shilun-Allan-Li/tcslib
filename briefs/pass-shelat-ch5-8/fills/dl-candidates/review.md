# Review of the DL fill brief (`fills/dl-candidates/brief.md`, units dl-a, dl-b, dl-c)

**Verdict: do not issue at #210's head.** Two prerequisite groups that the routes need are still
missing after #210 (F1, F2). Once they land on the campaign branch, the brief can be issued after
the edits below (F3 to F12).

Checked against PR #210 head `fff0430c7c9db136e60ed14b069e972c2ea56fc8` (worktree `$SP/wt-e1`, olean
tree `$SP/e1-oleans`). Lean was run one process at a time through `scripts/lean_check_tree.sh`, never
`lake build`. Logs and probe sources are in `$SP/review/dl-candidates/`
(`$SP` = `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`).

## Findings

### F1 (blocker): the `Foundations/Experiments.lean` equations did not land

The brief's prerequisite row `predProb_eq`, `invProb_eq`, `distAdv_eq` (brief :217) is not in #210.
`decls.tsv` has no row for `Experiments.lean`, the file is not in `changed-files.txt`, and E1a lists
it as out of scope (E1a-REPORT :71). The probe confirms all three names are unknown in every owned
scope. `acceptProb` has no body equation either. The brief never asked for one, but dl-c needs it.
Probe U4/S9 shows `predProb` cannot be read once sealed.

Blocked targets under rule 10:
- **dl-b:** `uprob_trial_ge` (its hypothesis `hA` is a `predProb`), `invProb_shiftInverter_ge`
  (its conclusion is an `invProb`) and the headline. The headline's per-instance success "is
  `predProb (expo g_u) …`", and it reads `invProb_dlInverter_ge`'s `invProb`. Possibly
  `uprob_majOracle_ne_le` and `invProb_dlInverter_ge` too, if they cannot pass the hypotheses
  through unchanged.
- **dl-c:** `elGamal_secure`. `GroupPKScheme.Secure` and `Ensemble.indist_iff_exists_negligible`
  are stated with `distAdv`, and the hybrids compare `acceptProb`s with `uprob`s.

PR #195 already has these four equations in the same file, `Foundations/Experiments.lean` on
`cryptography/pass-shelat-ch5-8-s2b`, commit `bd2e4d0f`: `invProb_def`, `predProb_def`,
`acceptProb_def`, `distAdv_def`, all `rfl`. #195 also has a `Games.Bridge.invProb_eq`/`predProb_eq`/
`distAdv_eq` with a *different* meaning (bridges to the game framework). So landing the equations
here as `…_eq` would put two names on one equation when the branches merge, and would reuse three
bridge names for something else. Land #195's `_def` lemmas on `cryptography/pass-shelat-ch2-4`
(that hunk alone, statements and docstrings identical) before `@ANCESTOR@`. The 3-colouring brief's
P7 (`distAdv_eq`) has the same gap.

**Suggested brief edit:** in the Prerequisites table, replace the row

> | `predProb_eq`, `invProb_eq`, `distAdv_eq` | `Foundations/Experiments.lean` | the bodies (…) | … |

with

> | `invProb_def`, `predProb_def`, `acceptProb_def`, `distAdv_def` (as in #195, commit `bd2e4d0f`) | `Foundations/Experiments.lean` | `invProb f A = uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1`; `predProb f B A = uprob fun z : α × ρ => A (f z.1) z.2 = B z.1`; `acceptProb X D = uprob fun z : σ × ρ => D (X z.1) z.2 = true`; `distAdv X Y D = |acceptProb X D − acceptProb Y D|` | dl-b `uprob_trial_ge`, `uprob_majOracle_ne_le`, `invProb_shiftInverter_ge`, `invProb_dlInverter_ge`, headline; dl-c `elGamal_secure` |

Also keep "**Before issue:** these land in `@ANCESTOR@`" for this row.

### F2 (blocker for dl-b, major for dl-a): no published identification of the collection's generator coins with `G.gen`'s

`HardCore`, `SampleClose` and `invProbAt` average over `r : F.gen.Coins n` with
`F.gen = expGen G`. `FullLengthExcept` (`hbig`) and `dlProb` (`hDL`) average over
`r : G.gen.Coins n`. The two types agree only by unfolding `expCollection`, `expGen`,
`NUPPT.ofPolyTimeUniform` and `NUPPT.coinLen`. The existing statements `expGen_runAt`
(DiscreteLog :512), `expCollection_index` (:704), `expCollection_index_of_lt` (:711) and
`dlCollection_index` (:868) take `r : G.gen.Coins n` where the other type is expected. E1b's
statement probe found them (E1b-REPORT §1: "reads the `gen` field"), but #210 did not restate
them. The brief lists `expCollection_index(_of_lt)` as "already published and sufficient"
(:235). They are not:
- **dl-b (probe S1–S3):** sealed, `r : (fullDLCollection H G).gen.Coins n` cannot be used as a
  `G.gen.Coins n` (S1). `expCollection_index` cannot be applied to it (S2). Published lemmas get
  only as far as `(expGen G).coins.eval n = G.gen.coins.eval n`, and nothing closes that (S3: there
  is no `expGen` coin lemma). Unsealed, U1 and U2 pass, so the route works only by reading
  DiscreteLog's `expCollection`/`expGen`. That is a rule-10 violation dl-b cannot avoid: it cannot
  link `hbig` and `hDL` to the `HardCore` average.
- **dl-a (probe SA1/SA2):** inside its own file dl-a can derive the length equality
  (`coinLen_eq`, `unfold expGen`, `coins_ofPolyTimeUniform`: SA2 passes). But
  `expSampler_spec`, `expCollection_sampleClose` and `expCollection_invProbAt_le` are sketched
  "through `expGen_runAt`" and with "the coin types identified (`expCollection_index`)". Those
  routes rely on the PPT definitions reducing. With `NUPPT.coinLen` and
  `NUPPT.ofPolyTimeUniform` sealed, even the *statement* of `expGen_runAt` fails to elaborate
  (SA1). So a sealed copy of `DiscreteLog.lean` cannot compile as the brief requires.

**Needed before issue** (R-04-5 (A): statements that elaborate only by reducing another file's
definition are restated). This goes in a follow-up to #210, in `DiscreteLog.lean`, because dl-a may
not add public lemmas and dl-b may not read `expGen`. For example:
- `expGen_coinLen (G) (n) : (expGen G).coinLen n = G.gen.coinLen n`;
- `expGen_coinsEquiv (G) (n) : (expGen G).Coins n ≃ G.gen.Coins n`
  (`Equiv.arrowCongr (finCongr (expGen_coinLen G n)) (Equiv.refl Bool)`), with
  `List.ofFn (expGen_coinsEquiv G n r) = List.ofFn r`;
- `expGen_runAt`, `expCollection_index`, `expCollection_index_of_lt` and `dlCollection_index`
  restated for `r : (expGen G).Coins n` (resp. `(C).gen.Coins n`), with `G.gen.runAt n []
  (expGen_coinsEquiv G n r)` on the right;
- optionally `fullDLCollection_index` beside `fullDLCollection`.

Only dl-a's sketches cite these statements, so the restatement ripples nowhere else (grep).

**Suggested brief edits:**
- Add a Prerequisites row: "`expGen_coinLen`, `expGen_coinsEquiv` and the restated `expGen_runAt`,
  `expCollection_index(_of_lt)`, `dlCollection_index` | `Candidates/DiscreteLog.lean` | (forms
  above) | dl-a `expSampler_spec`, `expCollection_sampleClose`, `expCollection_invProbAt_le`; dl-b
  headline (moving between the `HardCore` coins and `G.gen`'s for `hbig` and `hDL`)".
- In the dl-b section, add: "The `HardCore` average is over `(fullDLCollection H G).gen.Coins n`;
  `hbig` and `G.dlProb` are over `G.gen.Coins n`. Move between them with `fullDLCollection_gen`
  and `expGen_coinsEquiv` (`HardcoreBit.uexp_comp_equiv`), never by `show`/defeq."
- Remove `expCollection_index(_of_lt)` from "Already published and sufficient" until they are
  restated.

### F3 (major): the base sorry count changed (75 to 78); `inputs/*/base-sorries.txt` are stale

`fillinputs.py` at `fff0430c…` gives, for each of the four owned modules: order **94** (identical
to the committed `order.txt`) and roots **75** (identical), but base sorries **78 in 15 modules**.
`Candidates/Factoring` goes 8 to 10 and `Candidates/RSA` 9 to 10: these are #210's shared
statements S1–S3. The units' own rows are unchanged (7 + 7 + 7). The brief tells workers that
"a sorry outside your rows … count must not change", so a worker sweeping against the stale 75
would see a mismatch it cannot explain.

**Suggested edits:**
- Regenerate `inputs/dl-{a,b,c}/base-sorries.txt` at `@ANCESTOR@` and commit them before issue.
- In the Build inputs table (:73–75) replace "75 in 15 modules" by "78 in 15 modules"
  (three times).
- In the Pre-ship record (:296–299) add: "At #210's head (`fff0430c`) the order lists and roots
  are unchanged (94, 75); the base sorry set is 78 (Factoring 10, RSA 10: the shared statements
  S1–S3, not yours)."

### F4 (major): existing proofs in the owned files fail in a sealed copy; authorize their re-points, or say where the seal goes

The seal (:269–272) seals "every other-file TCSlib definition your proofs mention". The fills
will mention `ExpValid` and `WellFormedIndex`. A sealed copy then fails on existing, non-target
proofs that destructure those `Prop` definitions by defeq:
- **dl-b:** `halfPred_eq` (DiscreteLogHardcore :555, `have := h.1.two_le` on `h : ExpValid i`).
  Probe S4 fails sealed. `((expValid_iff i).1 h).1.two_le` passes (S5).
- **dl-c:**
  - `ddhExpo_statClose` (ElGamal :279, `hv.2.2.1` on `ExpValid`): probe C3 fails sealed.
  - `egGroupGen_valid` (:797) and `egGroupGen_wellFormed` (:824), `obtain ⟨a, b, c, …⟩ :=
    G.wellFormed …` on `WellFormedIndex`: probe C1 fails sealed ("not an inductive datatype").
    The same through `(wellFormedIndex_iff n _).1` passes (C2).
- **dl-a:** the statements of F2 (SA1).

Ground rule 1 (only the listed `sorry` bodies change) forbids fixing any of these. The one
authorized re-point (`halfStr_spec`) is also not reconciled with it.

**Suggested replacement** for the "Authorized re-point" paragraph (:52–54):

> **Authorized re-points (proof-only; statements unchanged).** Rule 10 and the seal reach these
> existing proofs in your file. Re-point them, and nothing else outside your targets:
> - dl-b, `halfStr_spec` (DiscreteLogHardcore ≈:568), which reads `expEnc` and `dlP` with `simp`:
>   `rw [expEnc_eq]; unfold halfPred; rw [dlP_eq]; simp only [halfStr, pairFstD_pairEncode,
>   pairSndD_pairEncode, listToNat_natToList (val_lt_two_pow_dlW i x)]`. Note that `simp only
>   [dlP_eq]` is not enough: it leaves `dlP i` inside the `Decidable` instance of `halfPred`, and
>   the goal no longer closes sealed. `rw` rewrites the instance too (review probe S6/S6b).
> - dl-b, `halfPred_eq` (≈:555): `have := ((expValid_iff i).1 h).1.two_le`.
> - dl-c, `ddhExpo_statClose` (ElGamal ≈:279): read `hv` through `(expValid_iff i).1 hv`.
> - dl-c, `egGroupGen_valid` (≈:797) and `egGroupGen_wellFormed` (≈:824): destructure
>   `(wellFormedIndex_iff n _).1 (G.wellFormed n r' hn)`.
>
> List each re-point in `REPORT.md`.

And in Ground rule 1, append: "…plus new private helpers under your unit's prefix, and the
authorized re-points above."

### F5 (minor): the seal does not catch `simp`/`unfold` reads

Probe C4: `simp only [expEnc]` closes with `expEnc` sealed. `attribute [local irreducible]` blocks
defeq reads only. Equation lemmas still fire under `simp [f]`, `unfold f` and `rw [f]`. Rule 10
forbids those too (ground rule 2). **Add to the seal item (:269):** "The seal catches definitional
reads only. Also grep your diff for every other-file definition name inside `simp`, `simp only`,
`rw`, `unfold`, `dsimp` and `delta` lists, and record the (empty) result."

### F6 (minor): rewrite the Prerequisites section as landed, with exact names

The section still reads as a request ("A prerequisite PR lands them … the forms below are what
that PR is asked for", :206–209). All rows except F1's landed in #210, under the asked names and
forms. Probe `#check` output matches each formula:
- `firstHit_eq`, `statClose_iff` (stated with `∀ T : γ → Prop`), `NUPPT.coinLen_eq`,
  `NUPPT.distinguisherL_eq`;
- `Collection.sampleClose_iff`, `invProbAt_eq`, `hardCore_iff`, and also `Collection.index_eq`;
- `divModStr_pairEncode`, `xgcdStr_pairEncode`, `sizeStr_eq`, `natToList_eq`;
- `dlP_eq`, `dlM_eq`, `dlG_eq`, `expValid_iff`, `wellFormedIndex_iff`, `safePrimeValid_iff`;
- `ExpGroupGen.fullLengthExcept_iff`, `ExpGroupGen.dlHard_iff`, `ExpGroupGen.dlProb_eq`, `expF_eq`;
- `expEnc_eq` (new).

The `expCollection` row is now `expCollection_domEquiv`, `_domEquiv_uprob`, `_f`, `_encD`,
`_decD`, `_gen`, `_sample`, `_eval`, plus the `dlCollection_*` and `fullDLCollection_*`
families.

**Suggested replacement** for :206–209: "Rule 10 forbids reading another file's TCSlib definition
except through a published lemma. The equations below are published at `@ANCESTOR@`: #210 for
all rows but the `Experiments.lean` row, which comes from #195's `bd2e4d0f`. Use them under these
names." Then turn the table's "Form" column into "Statement (as published)". Fold the
`DiscreteLog.lean` paragraph (:224–226) into "dl-a may unfold its own definitions, but prefer
these lemmas."

### F7 (minor): status block

:9–12 says the four files are unchanged since #206. #210 changed three of them: `Concrete`
(`DistinctPrimes.p_eq` and the like), `DiscreteLog` (equations, domain equivalences) and
`DiscreteLogHardcore` (the `fullDLCollection_*` interface and the restated headline). `ElGamal`
is unchanged. **Suggested addition:** "The equation-lemma PR #210 (merge `<hash>`) added rule-10
equations to `Concrete`, `DiscreteLog` and `DiscreteLogHardcore`, the published domain equivalence
`fullDLCollection_domEquiv` with its field equations, and restated `fullDLCollection_hardCore`
(ruling R-04-5 (A)). `ElGamal` is unchanged." Replace "**Before issue:** the rule-10 prerequisites
below land in `@ANCESTOR@`" by "**Before issue:** F1's and F2's prerequisites land, and the inputs
are regenerated."

### F8 (minor): dl-b section, interface list and the `ZMod` transport

:106–107 lists `fullDLCollection_domEquiv`, `_domEquiv_uprob`, `_f`, `_encD` and `_decD`.
- Add `fullDLCollection_gen` (the only way to `expGen G`, F2), and `fullDLCollection_sample`/`_eval`
  for completeness.
- The concrete lemmas are stated on `ZMod (p − 1)` with `[Fact p.Prime] [NeZero (p − 1)]`, while
  the domain is `ZMod (expOrd i)` with `expOrd i = dlM i = dlP i − 1` (`expOrd_of_valid`,
  `FullGroupValid`). Name the Mathlib transport: "move from `ZMod (expOrd i)` to `ZMod (p − 1)`
  along `ZMod.ringEquivCongr` (`ZMod.ringEquivCongr_val` for `halfPred_eq`); both resolve in the
  file's scope". Probed: both are present.

### F9 (minor): the lint line will not read "0 FAIL"

`python3 scripts/campaign_style_lint.py TCSlib/Cryptography/Candidates` at #210's head gives
8 FAIL: Rabin ×7, plus `ElGamal.lean:749`, "sorry without a proof sketch". That is
`polyTimeComputable_egGroupGenRaw`, whose frozen docstring has no "Proof sketch" label. **Replace
:273** by: "lint: no FAIL in your owned files' rows (`python3 scripts/campaign_style_lint.py
TCSlib/Cryptography/Candidates`). Rabin's FAILs are not yours. `ElGamal.lean:749`
(`polyTimeComputable_egGroupGenRaw`) clears when that target is filled; if it stays partial, the
FAIL is pre-existing."

### F10 (minor): attachment wording and the evidence path

- :261 "Use the environment addendum attached at dispatch". The protocol has no attachments
  (EXCHANGE.md ruling). Replace by "Use the environment addendum `fill-environment-addendum.md`
  (v1), in `outbox/fills/dl-candidates/` on the exchange branch beside this brief (also at
  `briefs/pass-shelat-ch5-8/fills/` in the repository)".
- :33–34: the addendum writes logs under `evidence/logs/`; say "`evidence/logs/`".

### F11 (minor): escalation for a missing prerequisite

:238–239 says to report it but not what to do with the target. Add, as the 3-colouring brief
does: "If a step needs a definition that has no published equation at `@ANCESTOR@`, mark that
target *blocked* (escalation E-API) with the missing lemma's statement, and go on with the next
target. Do not read the body."

### F12 (minor): import wording, dl-c

:263 "75 modules, unless you add the one authorized import". The optional
`import …DiscreteLogHardcore` adds no Mathlib root: its Mathlib imports are already in ElGamal's
closure, and the module is already in the order list. Say "75 modules (the authorized import adds
none)".

### Checked, no finding

- **Targets:** each unit's target list equals the `sorry`s of its owned files at #210's head:
  Concrete 1 + DiscreteLog 6, DiscreteLogHardcore 7, ElGamal 7. The restated headline quoted at
  :104 is byte-identical to the source (:648).
- **Routes:** the headline's constants check out:
  - with `ε = 1/(2n^c)` and `ℓ = 16n^{2c+1}`, `k/(ε²ℓ) = 1/4`;
  - the coins are `n² + 16n^{2c+4} + 16n^{2c+2}·A.coinLen n`;
  - the loss is `(1 + 16n^{2c+2})2^{−n}`;
  - `(ε/2)·3/(4·16n^c) = 3/(256n^{2c})`.

  The "Name corrections" still hold, and the corrected names resolve in DiscreteLogHardcore's and
  ElGamal's scopes. The Mathlib names of `mathlib-overlap-nt.md` for dl-b and dl-c resolve.
- **Parallel safety:** the owned files are disjoint. Cross-unit uses are statements only
  (`statClose_sampleBelowL`). dl-c's optional import creates no cycle.
- **Protocol:** repository, branch, `@ANCESTOR@`/`@ISSUED@` placeholders, `fill/<unit>` never
  pushed, `inbox/fills/<unit>/` with `REPORT.md`/`patches/`/`src/`/`evidence/`, checkpoint and final
  commit messages, rebase-before-push, statement freeze and budget order are all present. Apart
  from F10, there is no zip or attachment language.

## Probe results

Probe sources and logs: `$SP/review/dl-candidates/ReviewDL{a,b,c}.{lean,log}` (run copies in
`$SP/wt-e1/Probe/`). Each is `#check @Name` for every Lean name the brief cites, the
prerequisites, the new #210 interface and the route's Mathlib names, in the owned file's
namespace and `open`s, followed by seal tests (`attribute [local irreducible]` in a section, each
with an unsealed control). The `fillinputs.py` outputs at `fff0430c` are in `fi-*`, the lint
output in `lint-head.log`.

| Probe | Names | Unresolved |
|---|---|---|
| ReviewDLa (DiscreteLog scope) | 171 | 55: other units' names; the † templates; the HardcoreBit majority/pairwise names and `Ensemble.indist_iff_exists_negligible`, which dl-a does not use; and the F1/F2 names |
| ReviewDLb (DiscreteLogHardcore scope) | 200 | 29: dl-c's names; the † templates; `Ensemble.indist_iff_exists_negligible` (expected, not imported); **`invProb_eq/_def`, `predProb_eq/_def`, `distAdv_eq/_def`, `acceptProb_eq/_def`** (F1); `expGen_coins` (F2, absent) |
| ReviewDLc (ElGamal scope) | 190 | 34: dl-b's names; `dlog`/`dlBits_pow` (expected, optional import); the † templates; the **F1 names**; `expGen_coins` |

Every other name resolves with the cited meaning, including all of #210's prerequisite lemmas
(F6) and the `fullDLCollection_*` interface.

Seal tests (each unsealed control passes):

| Test | Sealed | Result |
|---|---|---|
| S1 `(fullDLCollection H G).gen.Coins n` used as `G.gen.Coins n` | `expCollection expGen NUPPT.coinLen NUPPT.ofPolyTimeUniform …` | fails (F2) |
| S2 `expCollection_index` at the HardCore coin type | same | fails (F2) |
| S3 coin lengths via `fullDLCollection_gen`, `coinLen_eq` | same | stuck at `(expGen G).coins.eval n = G.gen.coins.eval n` (F2) |
| SA1 statement of `expGen_runAt` | `NUPPT.coinLen NUPPT.ofPolyTimeUniform` | fails to elaborate (F2) |
| SA2 `(expGen G).coinLen n = G.gen.coinLen n` (dl-a, `expGen` own) | same | passes |
| S4 `h.1.two_le` on `ExpValid` (`halfPred_eq`) | `ExpValid` | fails (F4) |
| S5 via `expValid_iff` | `ExpValid` | passes |
| S6 `halfStr_spec` with `simp only [dlP_eq]` | `expEnc dlP` | fails: the instance keeps `dlP` (F4) |
| S6b `halfStr_spec` with `rw [expEnc_eq]; unfold halfPred; rw [dlP_eq]; simp only …` | `expEnc dlP` | passes |
| S7 restated headline elaborates | `expCollection …` | passes |
| S8 pre-#210 headline (control) | `expCollection …` | fails, as #210 intended |
| S9 / U4 `predProb` read | `predProb` | fails (F1) |
| distAdv read (dl-c) | `distAdv` | fails (F1) |
| C1 `obtain` on `WellFormedIndex` (`egGroupGen_valid`) | `WellFormedIndex` | fails (F4) |
| C2 via `wellFormedIndex_iff` | same | passes |
| C3 `hv.2.2.1` on `ExpValid` (`ddhExpo_statClose`) | `ExpValid` | fails (F4) |
| C4 `simp only [expEnc]` | `expEnc` | passes: the seal does not catch simp reads (F5) |
