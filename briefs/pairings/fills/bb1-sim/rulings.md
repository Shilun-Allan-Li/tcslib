# bb1-sim · Seyoon's rulings on design note r1 (2026-11-16)

These rule on the eleven questions of `design-r1.md` §5. Eight are as recommended; Q6, Q10 and Q11 are changed.

| # | Ruling | |
|---|---|---|
| Q1 | A **new module `Games/Relational.lean`**, imported by the `Games` facade. | as recommended |
| Q2 | The names are `Games.ProbComp.expect_simulate_rel`, `prob_simulate_rel` and `expect_sample_rel`, beside `ProbComp.expect_simulate_congr`. | as recommended |
| Q3 | The **inline expectation form** of the per-call hypothesis: from `R s t`, test functions that agree at equal answers and related states have equal expectations after one call. | as recommended |
| Q4 | The statement phase includes the companions `prob_simulate_rel` and `expect_sample_rel` with the target. | as recommended |
| Q5 | **No query budget now.** DL-40's cleanup either promotes the budgeted ETT lemmas `expect_simulate_abs(_inv)` as they are, or adds a budgeted relational variant when it is needed. | as recommended |
| Q6 | **Promote the averaging bound `\|𝔼 f − 𝔼 g\| ≤ 𝔼 h` into `Games/Probability.lean`**, as a public lemma beside the constant-bound `ProbComp.abs_expect_sub_le`. It is part of the statement phase, so expect a larger rebuild and re-seal. The private ETT copy (`EncryptThenTag/Forgery.lean:515`, DL-40) is re-pointed to it in the cleanup. | **changed** (was: public in `Relational.lean`) |
| Q7 | **One reader, `IBEScheme.sidImpl_eq_oracleImpl`,** in `Defs.lean` after T4's `_onSpec` readers. It is carried by the bb1-sim PR as a pure insertion, under an advance scope ruling confirmed by a probe first, which also fixes any needed `encCT` reader. | as recommended |
| Q8 | **One bb1-sim gate after Gate 44.** It covers the Games statement phase (`Relational.lean` and the `Probability.lean` addition), the reader insertions and the T2/T3 fill. | as recommended |
| Q9 | The Games statement phase is **its own small PR on the records tip**. The fill is stacked on T4's PR, or based on the tip once T4 merges. | as recommended |
| Q10 | **The group helpers go into the frozen `Pairing/Group.lean`** by an approved reader-style insertion beside the published `G_T` bijection: `Z_p ≃ G` for `g ≠ 1`, the additive exponent laws in `G`, and identity injectivity on good coins. Reuse Mathlib's `orderOf`/`ZMod` API where it applies. | **changed** (was: public helpers in the fill) |
| Q11 | **Ingest and cite [BGZ09] and [Sho04]** for the relational simulation lemma. Seyoon sends the PDFs. As with Gen09, nothing waits: the statements proceed, and the citations are a docstring-only follow-up after the ingest. No Lean docstring cites either tag before then. | **changed** (was: framework lemma, no tags) |

Next:
- the probe that fixes the reader set (after T4's readers land);
- the Games statement-phase PR (`Relational.lean` with the targets; the averaging bound in `Probability.lean`);
- the bb1-sim fill.
