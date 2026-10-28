"""One-line justifications of the after screen's new pairs. Usage: pair_just.py <screen-diff> <out.md>"""
import re
import sys
diff, out = sys.argv[1:3]
BANK = re.compile(r"^QyKit\.(b\w+|K)$")
ROWS = {"qy_copy", "qy_copy_over", "qy_transfer", "qy_clear", "qy_writeConst", "qy_rewind"}
BOUNDS = {"qyTestS", "qyTestP", "qyRndS", "qyRndP", "qyCk", "qyDk", "qyMidB", "qyTopB"}
SPECS = {"QySpec", "QyInSpec", "QyClockSpec"}
def just(a, b):
    s = {a, b}
    if all(BANK.match(x) for x in s):
        return "two banks' one-line `qyBank` definitions (or a bank's offset spelling `QyKit.K`'s sum): same shape by construction, different tapes and offsets"
    if s <= ROWS:
        return "two catalog rows' normal-form readings: different published rows (`copyMapTM`, `transferMapTM`, `clearTM`, `writeConstTM`), different endpoints"
    if s <= BOUNDS:
        return "two explicit time bounds of the same shape, for different runs"
    if s <= SPECS:
        return "the call clauses: an install call (an argument), an input call (the blank seam), the clocked call (its two exits); one statement each"
    if all(x.startswith("qy_unpair_succ_") for x in s):
        return "the four cases of `Nat.unpair`'s successor rule, each the same three-line argument on a different case"
    if s in ({"qy_mid_run", "qy_top_run"}, {"qy_mid_code", "qy_top_code"}, {"qy_midB_le", "qy_topB_le"},
             {"QyMPh", "QyTPh"}, {"qyMidM", "qyTopM"}):
        return "the two writers' parallel parts: different phases (`g`'s input call or the square's install call, the seek), tails and hosts"
    if s in ({"qy_setup_long", "qy_setup_short"}, {"qy_main_long", "qy_main_short"}):
        return "the long and short paths through the same host: the short one is a prefix of the long one's phases"
    if s <= {"qy_clockHost_finish", "qy_clock_start", "qy_expand_start", "qy_expandHost", "qy_wordPatch_ones"}:
        return "the clock's and the expansion's start and exit readings: shared hypothesis lists (the bank, the counter), different conclusions"
    if s <= {"qy_hosted'", "qy_hosted_last"}:
        return "the phase host's segment with and without a final dispatch (`phaseHostTM_run` against `phaseHostTM_run_le`)"
    if s <= {"qy_rndS_le", "qy_rndP_le"}:
        return "the stopping and the passed round's bound simplifications: same expansion pattern, different bounds"
    if s <= {"qy_ones_val", "qy_rung_val"}:
        return "the counter values of `1^m` and `0^m 1`, each by induction on `m`"
    if s <= {"qy_two_pow_bits_le", "qy_log_bits", "qy_lt_two_pow_bits"}:
        return "`Nat.bits` length facts, each through `qy_log_bits`'s `Nat.log` reading"
    if s <= {"qy_not_scratch_ge", "qy_not_scratch_tp"}:
        return "the two off-scratch facts (bank blocks, named tapes): the same case split on the clock's bank"
    if s <= {"qy_ledger", "qy_sum_affine"}:
        return "two sums over `Finset.range`, each by `Finset.sum_range_succ` induction"
    if s <= {"qyAt2_move", "qy_moveOne"}:
        return "head-move equations for the comparator and for one tape"
    if s <= {"qy_loop", "qy_notStop"}:
        return "the escape set's membership test (`qyLocE`) read in both"
    if s <= {"qy_call", "qyC_mapState"}:
        return "the `Cfg.mapState` field-equation idiom around a seam (`qy_call`'s conversions)"
    return "REVIEW"
rows_in, rows_x = [], []
for l in open(diff):
    m = re.match(r"^NEW \[(.*?)\] (\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%", l)
    if not m:
        continue
    kind, t, sname, x, y, pct = m.groups()
    a = t.split("::")[-1]; b = sname.split("::")[-1]
    if kind == "in-file":
        rows_in.append(f"| `{a}` | `{b}` | {pct}% | {just(a, b)} |")
    else:
        rows_x.append((t, sname, pct))
XD = {
    "qy_run_one": "idiom: the one-step identity `M.runFrom c 1 = M.step c` (from `runFrom_succ_eq_step'`, `runFrom_zero`), inlined in those proofs; no public lemma states it (`CfgRecord`'s `recordStep_runFrom_one` is private there): promotion candidate for `Deterministic`",
    "qyC_mapState": "idiom: the `Cfg.mapState` field equations around `Cfg.ext` (the accepted idiom pairs' pattern; this file's is a third), no lemma re-derived",
    "emitAction": "idiom: the model's one-symbol emission action; `FinTM.emitAction` halts at its chain's end, which the emitter's prefix cannot (it continues to its scan), so it is not reusable here",
    "sl_rewrap": "idiom: `seamReleaseTM_runFrom_pos` and the `Cfg.mapState` field equations around a seam (`SeamLayout` is a model to read; no lemma re-derived)",
    "b2_unary_run": "idiom: a run lemma's statement shape over a unary tape; a different machine (L2's comparator against `Nondeterminism`'s unary decider)",
}
with open(out, "w") as f:
    f.write(f"**Cross-file pairs ({len(rows_x)})**, each with an owned-file declaration on one side:\n\n")
    f.write("| target | source | share | disposition |\n|---|---|---|---|\n")
    for t, sname, pct in rows_x:
        key = next((k for k in XD if k in t or k in sname), None)
        f.write(f"| `{t}` | `{sname}` | {pct}% | {XD.get(key, 'REVIEW')} |\n")
    f.write(f"\n**In-file pairs ({len(rows_in)})**, each with its justification:\n\n")
    f.write("| target | source | share | justification |\n|---|---|---|---|\n")
    f.write("\n".join(rows_in) + "\n")
print(len(rows_x), len(rows_in), sum(1 for r in rows_in if "REVIEW" in r))
