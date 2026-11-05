# Semantic search per new private (E-D fill)

**By name.** None of the 106 names below, nor any identifier starting with `dz`/`Dz`, occurs in any
`.lean` file of the base tree or of the 182 pull-request heads visible on the remote
(`refs/pull/*/head`, open and closed; the REST API is not available to this session, so all were
searched), and in the current tree only the owned file has them (pr-and-base-hits.txt: empty).

**By statement.** `evidence/probes/DzExactProbe.lean` restates every new lemma whose statement
involves only public definitions and runs `exact?` (evidence/logs/exact-probe.out). It found one
re-derivation, a former `dz_pairEncode_length` = the published `Turing.length_pairEncode`: it was
removed and the published lemma is cited. Every other new lemma states a run of this file's own
machines (`dzQ`, `dzSet`, `dzTakeTM`, …) over its own layout (`qyC`, `dzLay`, `DzKit`), so no library
statement can match it; the text screens cover copying.

| Declaration | Kind | Statement search |
|---|---|---|
| `DzClockSpec` | def | definition: name search and screens |
| `DzKit` | structure | definition: name search and screens |
| `DzKit.K` | def | definition: name search and screens |
| `DzKit.bA` | def | definition: name search and screens |
| `DzKit.bB` | def | definition: name search and screens |
| `DzKit.bB_ne` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.bG` | def | definition: name search and screens |
| `DzKit.bL` | def | definition: name search and screens |
| `DzKit.bP` | def | definition: name search and screens |
| `DzKit.bQ` | def | definition: name search and screens |
| `DzKit.bR` | def | definition: name search and screens |
| `DzKit.bR_j` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.bR_ne` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.bR_off` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.le_K` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.sB` | def | definition: name search and screens |
| `DzKit.sR` | def | definition: name search and screens |
| `DzKit.tp` | def | definition: name search and screens |
| `DzKit.tp_ne` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzKit.tp_val` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `DzPK` | inductive | definition: name search and screens |
| `DzPPh` | abbrev | definition: name search and screens |
| `DzQK` | inductive | definition: name search and screens |
| `DzQPh` | abbrev | definition: name search and screens |
| `dzAcc` | def | definition: name search and screens |
| `dzAlpha` | def | definition: name search and screens |
| `dzBlk` | def | definition: name search and screens |
| `dzBlk_length` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzClkEmb` | def | definition: name search and screens |
| `dzClkEmb_eqs` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzD` | def | definition: name search and screens |
| `dzK` | def | definition: name search and screens |
| `dzLay` | def | definition: name search and screens |
| `dzLay_const` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzLay_off` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzLay_tp` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzLay_update` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dzOne` | def | definition: name search and screens |
| `dzPKDecEq` | instance | definition: name search and screens |
| `dzPKFintype` | instance | definition: name search and screens |
| `dzPPhDecEq` | instance | definition: name search and screens |
| `dzPPhFintype` | instance | definition: name search and screens |
| `dzPexit` | def | definition: name search and screens |
| `dzQ` | def | definition: name search and screens |
| `dzQB` | def | definition: name search and screens |
| `dzQF` | def | definition: name search and screens |
| `dzQKDecEq` | instance | definition: name search and screens |
| `dzQKFintype` | instance | definition: name search and screens |
| `dzQM` | def | definition: name search and screens |
| `dzQPhDecEq` | instance | definition: name search and screens |
| `dzQPhFintype` | instance | definition: name search and screens |
| `dzQRed` | def | definition: name search and screens |
| `dzRej` | def | definition: name search and screens |
| `dzSet` | def | definition: name search and screens |
| `dzSetB` | def | definition: name search and screens |
| `dzSetL` | def | definition: name search and screens |
| `dzSetM` | def | definition: name search and screens |
| `dzSetRed` | def | definition: name search and screens |
| `dzTakeTM` | def | definition: name search and screens |
| `dz_K_bound` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_acc_ne_rej` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_accepts_iff` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_alpha_eq` | theorem | exact? (dzAlpha unfolded): no lemma |
| `dz_arg_bank` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_bank_off` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_budget_le` | theorem | exact?: no lemma |
| `dz_cell0` | theorem | exact?: only `rfl` (would unfold FinTM.bufferTape, not allowed); no lemma |
| `dz_clock_exists` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_core_word` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_emit_run` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_entry_vals` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_first` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_flag` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_hQ` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_halts` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_handoff` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_initCfg` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_kit_exists` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_mid_complete` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_mid_sound` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_norm` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_notF` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_ones_succ` | theorem | exact?: only `rfl`; no lemma |
| `dz_out_le` | theorem | exact?: no lemma |
| `dz_padded_value` | theorem | exact?: no lemma |
| `dz_qmid` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_qoff` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_qtop` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_query_mid` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_rewrite` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_runR` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_seg_read` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_setup` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_setup_facts` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_silent` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_silentCfg_eq` | theorem | exact?: no lemma (the silent companion of embedEmitCfg_eq) |
| `dz_split` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_split_stream` | theorem | exact?: no lemma; the same idiom as NDHost's private `guessRun_split` (screen pair 98%): keep, promotion requested |
| `dz_split_tape` | theorem | exact?: no lemma |
| `dz_tail_run` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_take_run` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_test` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_top_iff` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_top_run` | theorem | states a run or fact of the own machines/layout: no library statement can match |
| `dz_word_lt` | theorem | exact?: no lemma (ExhaustiveReplay's private `xr_val_lt` states it for its own `xr_val`: screen pair at 65%; keep, promotion requested) |
| `dz_zero_bank` | theorem | states a run or fact of the own machines/layout: no library statement can match |
