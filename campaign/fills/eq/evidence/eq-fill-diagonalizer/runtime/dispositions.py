"""Attach a disposition to every new pair of a screen diff (python3 -I dispositions.py <diff>).
Rules are keyed on the declarations' names; a pair matching no rule is printed as UNCLASSIFIED."""
import re, sys
rules = [
 (r'guessRun_split|dz_split_stream', 'copy of another file\'s private (NDHost `guessRun_split`, the three-line list split): keep, promotion requested'),
 (r'xr_val_lt|dz_word_lt', 're-derivation of another file\'s private (ExhaustiveReplay `xr_val_lt`, for its own `xr_val`): keep, promotion requested'),
 (r'a3n_poly_pair.*dz_alpha_eq', 'idiom: the rewrite chain `pairDecode_pairEncode`/`Option.map_some`/`getD_some`; different statements'),
 (r'dzBlk_length', 'idiom: a `simp only [List.length_append, List.length_replicate, List.length_singleton]` length computation'),
 (r'(clearTM|incrementTM).*dzTakeTM', 'idiom: a one-tape row\'s transition-table shape; `dzTakeTM` is the ruled own leaf (no row writes a blank at one cell)'),
 (r'DzKit\.b[ABLR]\b.*DzKit\.b[ABLR]\b', 'idiom: bank maps, `qyBank` at different offsets (as E-Q\'s `QyKit.bCb`, …)'),
 (r'DzKit\.s[RB].*DzKit\.s[RB]', 'idiom: the two instances of `dzClkEmb` (core, decider)'),
 (r'DzKit\.b[RB]_ne|DzKit\.bR_off.*DzKit\.bR_j', 'idiom: bank-tape disjointness facts'),
 (r'dz_zero_bank.*dz_arg_bank', 'idiom: the bank\'s heads beside the bank\'s tapes'),
 (r'dzSetL.*(qySetT5|qyTB)', 'idiom: a layout as a `Function.update` chain'),
 (r'qyLocRed.*dzSetRed', 'idiom: a phase host\'s dispatch table'),
 (r'dz_take_run.*(qy_step|qy_emit_halt)', 'required by the brief: the leaf\'s own step lemma (`qy_step` covers only steps that write nothing)'),
 (r'dz_tail_run.*qy_copy', 'required by the brief: `copyMapTM_run_ofCfg` directly from cell 1 (`qy_copy` assumes the word at cell 0)'),
 (r'dz_clock_exists.*qy_clock_start', 'idiom: the clock configuration\'s field reading, over `vhostSilentCfg` (the brief: state the clock\'s clauses afresh over `vhostSilentTM`)'),
 (r'dz_split.*(dz_tail_run|qy_wordPatch_ones)', 'idiom: a framed row\'s endpoint read cell by cell'),
 (r'dz_qmid.*dz_qtop', 'idiom: the two branches\' shared flag and tail preamble'),
 (r'dz_top_run.*(dz_flag|DzKit\.bB_ne)', 'idiom: a hosted phase and a bank fact'),
 (r'dz_accepts_iff.*dz_halts', 'idiom: the setup\'s facts fed to the host\'s halting and acceptance lemmas'),
 (r'qy_main.*dz_out_le', 'idiom: the `computesFunInTime_iff`/`computesInTime_iff` reading'),
]
lines = [l for l in open(sys.argv[1], encoding='utf-8') if l.startswith('  NEW ')]
for l in lines:
    m = re.match(r'  NEW\s+(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%', l)
    t, s, pct = m.group(1), m.group(2), m.group(5)
    key = f'{t} {s}'
    disp = next((d for rx, d in rules if re.search(rx, key)), 'UNCLASSIFIED')
    lab = lambda x: x.split('::')[0].split('/')[-1] + '::' + x.split('::')[1]
    print(f'- `{lab(t)}` ← `{lab(s)}` ({pct}%): {disp}')
