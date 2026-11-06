## E1 final: gate 07 equation-lemma PR (union of E1a and E1b)

All three statements are restated, and every combined check passes. I committed on `wip/eqlemmas` in `$SP/wt-e1` and did not push.

**Head:** `fff0430c7c9db136e60ed14b069e972c2ea56fc8`. That is the 7 unit commits plus one new commit.

### The three restatements
1. **`Candidates.fullDLCollection_hardCore`** (`Candidates/DiscreteLogHardcore.lean:646`). It stays sorried, with its docstring kept.
   - Old: `(fullDLCollection H G).HardCore halfPred`
   - New: `(fullDLCollection H G).HardCore fun i x => halfPred i (fullDLCollection_domEquiv H G i x)`
   - Sketch changes, wording only:
     - *Easy:* now adds "read through `fullDLCollection_encD`".
     - "the domain is `Z_{p−1}`" now cites `fullDLCollection_domEquiv` with `fullDLCollection_domEquiv_uprob`.
     - The `f_i x` step now cites `fullDLCollection_f`.
2. **`TrapdoorCollection.OneWay.glPad_tdpBitScheme_singleBitSecure`** (`Asymptotic/PublicKey.lean:960`).
   - Old: `(E : (T.glPad m henc).toCollection.PredEvaluator T.glBit)`
   - New: `(E : (T.glPad m henc).toCollection.PredEvaluator fun i z => T.glBit i (T.glPad_domEquiv m henc i z))`
3. **`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`** (`PublicKey.lean:978`).
   - Old: `∃ E : (T.glPad m henc).toCollection.PredEvaluator T.glBit, …SingleBitSecure`
   - New: `∃ E : (T.glPad m henc).toCollection.PredEvaluator fun i z => T.glBit i (T.glPad_domEquiv m henc i z), …SingleBitSecure`
   - Both PublicKey docstrings now say the predicate `⟨x, r⟩` is "read through `T.glPad_domEquiv`".

**Why the meaning is unchanged.** Both `fullDLCollection_domEquiv H G i` and `T.glPad_domEquiv m henc i` are `Equiv.refl` on the definition. So each new predicate is the old one composed with the identity, and the old and new statements are definitionally equal. The change is in how the predicate is typed: it now takes the collection's own domain `(F).D i` and reaches `ZMod (expOrd i)` or `T.D i × {0,1}^…` only through the published equivalence. Nothing else in the statements changed, including hypotheses and conclusions.

### One added declaration and the proof changes
- **Added** `TrapdoorCollection.OneWay.glPad_hardCore_domEquiv` (`Asymptotic/HardCoreCollection.lean:462`), beside the definitions. Statement: `(T.glPad m henc).toCollection.HardCore fun i z => T.glBit i (T.glPad_domEquiv m henc i z)`. Its proof is `h.glPad_hardCore m henc`, which is allowed because the definitions are in the same file. It has a docstring and is not `@[simp]`.
- **Why it was needed.** Under the seal, `T.glBit` cannot even be typed as a predicate on `(T.glPad m henc).D i`. So a proof in PublicKey can only get the new form from a lemma in glPad's own file.
- **Proof changes.** The two PublicKey proofs now use the new lemma in place of `glPad_hardCore`.
- **Consumers.** The only library consumer of the three statements is `audits/pass-shelat/Checks.lean`, which only runs `#print axioms`, so no consumer needed an edit. No other statement had to change.

### Check results (logs in `$SP/e1/final/`)
- **Replay** over the 33 changed files (union of both units plus my edits): all 116 downstream modules from `downstream2.py`, then `audits/pass-shelat/Checks`. All 117 have rc=0 and 0 errors (`replay-head.log`, full outputs in `full-head/`).
- **Sorry counts:** I counted the base myself on the same 117 modules (`wt-e1-base` at the base commit, against a copy of the base olean tree; `replay-base.log`, `full-base/`).
  - The base tree was missing 3 oleans (HardcoreBit/NoFixedBit, OneWayFunctions/Robustness, Pseudorandom/Functions). That made 4 base modules fail on import. I built the 3 missing oleans from base sources and re-checked; all 4 pass with 0 sorry (`replay-base-fix.log`).
  - Result (`sorry-compare.txt`): every module matches except `Candidates/Factoring` (8→10) and `Candidates/RSA` (9→10). Totals are 63 base, 66 head.
- **Checks output:** identical to the base, line for line (508 lines). The axioms of the three restated statements are unchanged: `fullDLCollection_hardCore` carries `sorryAx` (it is still sorried); the two glPad theorems use standard axioms only.
- **Axioms** of all 183 ADDED and 3 CHANGED declarations (`axioms.log`, `axioms-summary.txt`):
  - Nothing outside `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`.
  - A meta probe (`direct-sorry.log`) checks whether `sorryAx` appears in a declaration's own type, value or auxiliary declarations. It does only for the three new shared statements (`polyTimeComputable_samplePrimeL` and `statClose_samplePrimeL_pair` in Factoring, `statClose_sampleUnitL` in RSA) and for the still-sorried `fullDLCollection_hardCore`.
  - The other 68 `sorryAx` results are the concrete collections' `_f/_encD/_decD/_domEquiv/…` lemmas. They inherit it from base definitions that already carry `sorryAx`: `expCollection`, `dlCollection`, `fullDLCollection`, `factoringCollection`, `rsaCollection`, `rsaTrapdoor`, `rabinCollection`, `rabinBlumTrapdoor` (`axioms-base-defs.log`, run against the base tree).
- **Lint:**
  - `style_lint.py` on each changed file, head against base (`style-lint-head.log`, `style-lint-base.log`): the only new findings are the three approved size findings (Collections 1072, RSA 1077, Rabin 1105 lines). Head has fewer findings than base in Machines and Parties (E1a added docstrings there).
  - `campaign_style_lint.py --check8b` on all 11 changed directories (`c8-*-*.txt`, `check8b-diff.log`): no new FAIL. The only new WARNs are the same three size findings. No new names appear in any check-8 list.
- **Statement diff** (`decls.tsv`, `decls.py` against `05fe903f…`): 183 ADDED (including `expCollection_f/encD/decD` and `glPad_hardCore_domEquiv`) and exactly 3 CHANGED, the three restatements. Nothing was REMOVED.
- **Seal probes** (`probes/`). All three seal `expCollection`, `fullDLCollection`, `Collection.glPad`, `PermCollection.glPad` and `TrapdoorCollection.glPad` with `attribute [local irreducible]`, except the open control:
  - `probe-SealRestatedPass.log`, rc=0: all three new statements elaborate sealed, and both PublicKey proofs replay sealed, verbatim and through the library names.
  - `probe-SealRestatedControl.log`, rc=1: the three old statements fail sealed, each with "Application type mismatch" on `halfPred` or `T.glBit`.
  - `probe-OpenOldControl.log`, rc=0: without the seal the old statements elaborate, so the control failures come from the seal.

### Notes
- I added no line to HardCoreCollection's module docstring for the new lemma; that is optional.
- Older records still quote the old forms: `briefs/.../gate03b-review.md`, `evidence-r2/03b/repair.diff.txt` and `fills/dl-candidates/preship/import-probe-dl-b.log`. I left them alone because they are history.
- The dl-b fill now targets the restated `fullDLCollection_hardCore`, so its worker should know about the change.
- Nothing failed. `$SP/wt-e1-base` (a detached base worktree) and `$SP/e1-oleans-base` are left in place as evidence; remove them with `git worktree remove` and `rm` when they are no longer needed.
