# Review: deepen-1 delivery (`Complexity.savitch` by iterative deepening)

Reviewed: head `c7b179da` (base `fd97df61`) at `/home/user/tcslib-scratch/wt-dp`, the delivery at
`/home/user/tcslib-scratch/deliveries/deepen-1/x/`, against the brief `campaign/fills/ch34/briefs/ch34-fill-deepen.md`,
`policy.md`, `campaign/standards/TEMPLATE.md` and `campaign/duplication-ledger.md`. I only read files. I ran no Lean.
Paths `Deepen.lean` = `TCSlib/Complexity/SpaceComplexity/SavitchARM/Deepen.lean`, `Savitch.lean` =
`TCSlib/Complexity/SpaceComplexity/Savitch.lean` (lines at `c7b179da`).

**Verdict.** The claim holds as far as reading can tell. The pins and the frozen statement are exact, rule 10 is clean,
the seal is faithful, the binding route is followed and the logs support the sweep, sorry, axiom and lint claims. **Two
duplication majors** would each cost an external gate round, the same way gate 95's inline re-proofs did: published
lemmas are re-derived inside `have`s and in a conjunct. The semantic search missed both. Fix them, plus the minors
below, before landing.

## Findings (ranked)

| # | Sev | Where | Finding | Proposed fix |
|---|---|---|---|---|
| 1 | **major** (debt, FM5) | `Deepen.lean:657-658` (`hB`), `:750-751` (`h3`), `:777-778` (`hWB`); also `:436`, `:749`, `:781` | `2 ^ w ≤ 2 ^ (w * w)` is re-proved three times as `Nat.pow_le_pow_right (by norm_num) (Nat.le_mul_self _)`. That is term for term the published `Complexity.LogProg.SavitchARM.size_facts` (`SavitchARM/Recursion.lean:108`: `w < 2 ^ w ∧ 2 ^ w ≤ 2 ^ (w * w)`). It is in `Deepen`'s namespace and in its import closure, and `Search`/`Recursion` cite it 9 times. The `w < 2 ^ w` sites are its first conjunct. | Cite `(size_facts _).2`, and optionally `.1`, at all sites. Record "caught, no family" in the ledger, as gate 95 did. |
| 2 | **major** (debt, FM5) | `Deepen.lean:407-412` (`dp_bits_logSpace`, 2nd conjunct, `:409`+`:411-412`) | `(Nat.bits n).length ≤ logSpace n` is re-derived by `rw [Nat.size_eq_bits_len] … rw [logSpace_eq]; exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self _ n)`. That chain is exactly `length_bits_le_log` (`Machines/Bin.lean:146`), whose proof is `length_bits_le (Nat.lt_pow_succ_log_self …)` with `length_bits_le` = `rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr h`. The file already cites `length_bits_le` at `:842`, so `Bin` is imported. | Use `(logSpace_eq n).symm ▸ length_bits_le_log n`, or `.trans_eq`. |
| 3 | minor | delivery §7, `evidence/semantic/DeepenExact.lean:515-518` | Why 1–2 were missed: `exact?` was posed only to whole private statements. A three-way conjunction such as `dp_bits_logSpace` cannot close by `exact?`, and no `have`-level sweep was done (gate 95 rounds 3–5: every typed or untyped `have`/`obtain`, simp sets, rewrite chains). REPORT §7's "two hits" is therefore incomplete. | Before the gate, run the gate-95 sweep over every `have`/`obtain` and conjunct, and attach its output. |
| 4 | minor | `Deepen.lean:110-114` | `dpρ r = ⟨r.val, _⟩` is `Fin.castLE (by omega)`, and `dpρ_inj` re-proves Mathlib's `Fin.castLE_injective`. The delivery's own `exact?` closed it, by `injective_of_le_imp_le`, and kept the local proof anyway. | Define `dpρ := Fin.castLE (by omega)` and `dpρ_inj := Fin.castLE_injective _`, or record a disposition. |
| 5 | minor | `Deepen.lean:257-307`; REPORT §7 table | The disposition says "no register-file split in the tree". But `RegExt`/`RegExt.update` (`Machines/ARMProof.lean:362,370`) is exactly the block-on-ρ / own-off-ρ split, and `dpSt` is Mathlib's `Fin.append` up to `25 = 18 + 7` (`dpSt_ρ`/`dpSt_own` ≈ `Fin.append_left`/`append_right`). It is not a verbatim copy, but an auditor will ask about it. | Disposition `dpSt*` against `RegExt.update` and `Fin.append` in the REPORT, or re-express it through them. |
| 6 | minor | `Savitch.lean:24-26` | Status says "`Complexity.savitch` holds for every space bound `S ≥ logSpace` (…; constructibility is used only for this bound)". `savitch` assumes `SpaceConstructible`, and the parenthesis is unclear. | "`Complexity.savitch_of_logSpace_le` proves the inclusion for every `S ≥ logSpace`; `Complexity.savitch` follows, since space-constructibility includes `logSpace ≤ S` and nothing else of it is used." |
| 7 | minor | `Savitch.lean:47-48`; `:60-62` | The Design bullet says "stops by radius `sp |x| + 1`", but `sp` is undefined in this module (use `c · S |x| + 1`). In Main results, `savitch` now has no tag while `PSPACE_eq_NPSPACE` keeps "(Proved.)". | Fix the wording, and tag consistently or drop "(Proved.)". |
| 8 | minor | `Savitch.lean:78-80` | The `savitch_of_logSpace_le` docstring states the deviation from [AB09, Thm 4.14] (no constructibility) but does not tag its source. policy §2 (Deviations/declaration tags) asks for it. | Add "[Sip13, §8.1, proof of Theorem 8.5]" to that docstring. |
| 9 | minor | `Deepen.lean:813`; `:59-60`; `:592` | The public `deepen_contract` docstring opens "**The fill's main theorem**", a campaign label and a bare label under policy §2's Statement prose rule. The `DeepenContract` docstring says what the predicate is for, not what it asserts. The private `dp_fit` sketch cites "the block fit's `fit_edge_block`", a probe that is not in the tree. | State the assertions in plain words, e.g. "if `N` decides `L` in space `sp`, a register machine with five logspace deciders decides `L` with registers of at most `C (sp n + logSpace n + 1)²` digits". In `dp_fit`, drop the probe reference. |
| 10 | minor | REPORT §3, §8, §2, §6 | (a) It says `Deepen.lean` has "844 lines"; the file and the lint have 848. (b) "`codeK N ≥ 1` has no published lemma" is false: `Complexity.ExpBFS.two_le_codeK` (`ExpBFS/Main.lean:211`) exists, though the three-import rule makes it unreachable. It belongs as a promotion request (beside `codeK` in `Codec`). (c) The checkpoint zips `cp1–8` are claimed but absent from the delivery; by the REPORT's own account they are identical end-of-session copies, so they do not do the job of checkpoints. (d) The inspection table (`args.tsv`) has about 10 false `rw (no list)` rows, from the register name `rw` (e.g. Deepen 179, 180, 432). Its nested `rw [show … by simp [ho1]]` rows are mangled, and the default-set `simp [ho1]` at `Deepen.lean:468` is not listed as a call of its own. | Correct the REPORT, and regenerate `args.tsv` with a tactic-position-aware extractor. |
| 11 | minor/note | `Savitch.lean:56-62, 70-71` | The Main-results list and the `[Sip13]` reference were edited, which is outside region (d)'s literal list (savitch docstring, Status, Design). policy §1 and §2 require these edits. | Maintainer: accept them explicitly in the landing record. |
| 12 | note | `Deepen.lean:61`; `Savitch.lean:94` | `DeepenContract` is a public predicate with no `_iff`/`_eq` lemma (policy "Definitions land with their lemmas"; campaign-lint check-8 WARN, 80→81). `savitch_of_logSpace_le` reads it by `obtain`, and `NSPACE` by `rintro`, both cross-file. The brief pins and forbids a fourth declaration. | Pre-empt this under the pack's Known deviations. |
| 13 | note | `Deepen.lean:163-189` | Policy §1 (Hosts come first): `dpD` is a private iterative-deepening driver, which is a host by that definition. The brief designs it this way (three public declarations). | Pre-empt it in the pack. Consider a host-registry entry for a later harvest. |
| 14 | note | `Savitch.lean:6, 18-22` (not owned) | The intro paragraph still says the theorem goes via the configuration graph of `ConfigGraph`, and `import …ConfigGraph` now looks unused. | Maintainer follow-up, through a brief amendment or a later PR. |
| 15 | note | `Deepen.lean:837-842` | The argument `v ≤ 2^(W·W) → |bits (v+1)| ≤ W·W + 2` re-derives the private `bits_succ_le` (`Logspace/ISCountGenCorrect.lean:209`). That lemma is not citable. `dp_bd_blk` (`:311-319`) repeats `embed_guardLe`'s internal case split, which is not published. | Ledger row candidates; no action for this fill. |
| 16 | note | `evidence/logs/axioms.log`, `final-sweep.log` | Neither log carries a commit hash. `axioms.log` also has no TIMED/command line. | The maintainer's replay covers this. |

## Checks that passed

1. **Freeze and pins.** `savitch`'s statement is unchanged; only its body is now `savitch_of_logSpace_le S hS.1`.
   - `DeepenContract` (`Deepen.lean:61-67`) and `deepen_contract` (`:822-823`) match `DeepenRoute.lean.txt` text for text.
   - `savitch_of_logSpace_le` is the probe's proof, differing only in `LogProg.`/`LogProg.SavitchARM.` prefixes.
   - The only public declarations are those three. The 43 privates all carry `dp`/`Dp` prefixes.
   - `git diff --stat fd97df61 c7b179da` touches exactly the three owned files. The facade change is the import beside `Correct` and one two-line list entry.
2. **Rule 10.**
   - Every `rw`/`simp` argument is a theorem, a local hypothesis or the file's own definition (`dpOrc`, `dpSt`, `dpW`). `GuardLe` is an `abbrev`, which policy allows.
   - The `rfl` closures (`:212`, `:218`, `:264`, `:315`, `fin_cases` with `exacts`) reduce only the file's own definitions, `Matrix.vecCons` and `Fin` eta.
   - The `decide`s are `Fin` literal inequalities.
   - **The seal is faithful.** `DeepenSealed.lean` is the head file plus three lines at 59–61, sealing 35 definitions (the block fit's 22, `NoEdge`, the 4 loop-section definitions and 8 extensions). Its control list equals the sealed list. The unsealed and sealed control bodies are identical. The output has 35 `Type mismatch` errors at 35 distinct sealed examples and none in the unsealed section. The sealed copy exits 0. `ARMLoops`, `halvCount_loop` and `inputLength_loop` introduce no other definitions. `Savitch.lean`'s new proof is not sealed; it is the probe's proof.
3. **Screens.**
   - `screen-before.txt` is byte-identical to `logs/ch34-fill-deepen-screen-base.txt` (269 declarations, 96 pairs, 27,259 characters).
   - The after-screen's pair list equals the before list, so there is no new pair. (Its population does not include `Machines/Bin` or `SavitchARM/Recursion`'s `size_facts` statement shape, so it could not catch findings 1–2.)
4. **Route.**
   - The deciders are `![inputLenLang, initLang N, acceptLang N, stepLang N, edgeLang N]`, with `σE = ![0,1,4,3]` and `σA = ![0,1,2,3]`.
   - Both blocks go through one `dp_fit`, which has `fit_edge_block`'s shape (`← setSt_toV, ← outerSt_toV`, one `AHalt.embed_guardLe … (A_noVal 0) … (outerU_run …)`, the `_iff_orc` bridges and `decide_eq_decide`).
   - The entry chain `rs, rw, rK, rU, rV, rM` onto `fun _ => 0` is syntactic (`:431-433`).
   - Correctness goes through `noEdge_iff` (`:677`), `noEdge_of_lt` (`:736`, `:746`) and `mem_iff_reach_of_noEdge` (`:693`).
   - The search is not re-proved. The edge cases hold generically (`halvCount_loop` at `n = 0`, `dp_body`'s zero case).
5. **Logs.**
   - Final sweep: 196 TIMED lines, all exit 0, 0 `error:`, ending with `SWEEP COMPLETE`.
   - The sorry warnings are 25 in 9 modules, equal module by module to the base set less `savitch`.
   - The three axiom prints are on `[propext, Classical.choice, Quot.sound]`.
   - Lint: campaign 0 FAIL / 81 WARN over 112 files; style 0 findings in 2 files.
   - Bootstrap: 196/196, with the overlay's `deepen_contract` sorry at module 141.
   - `SHA256SUMS`: 54 entries, all match, nothing unlisted.
