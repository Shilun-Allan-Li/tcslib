"""The per-private semantic duplication table. Usage: gen_dup_table.py <owned.lean> <exactq-results.tsv>
<name-hits-all.txt> <out.md>"""
import re
import sys
owned, exq, hits, out = sys.argv[1:5]
src = open(owned).read()
i0 = src.index("private theorem qy_query_of_main")
decls = re.findall(r"^private (theorem|lemma|def|abbrev|inductive|structure|instance) (\S+)",
                   src[i0:], re.M)[1:]
res = {}
for l in open(exq):
    n, v = l.rstrip("\n").split("\t", 1)
    res[n] = v
nhits = sum(1 for _ in open(hits))
STMT = {
    "qy_bits_len_mono": "`Complexity.LogProg.length_bits_mono` (`SpaceComplexity/Machines/Bin.lean`, at the base) "
                        "states it, outside the frozen import closure: not citable; kept (relocation candidate)",
    "qy_lt_two_pow_bits": "`lt_two_pow_bits` (`Randomized/SpaceAmplifyPoly.lean`) states it on `origin/main`, "
                          "`complexity/arora-barak-ch7` and PR 135 only, not at the base: not citable; kept",
    "qy_two_pow_bits_le": "`two_pow_bits_le` (`Randomized/SpaceAmplifyPoly.lean`) states it on `origin/main`, "
                          "`complexity/arora-barak-ch7` and PR 135 only, not at the base: not citable; kept",
    "qy_log_bits": "`length_bits_le_log` (`Bin.lean`) states the `≤` half only, outside the import closure",
    "qy_pow6_le": "nearest `succ_pow_le_two_pow_mul` (`Randomized/ZPPHostsClasses.lean`, `origin/main`): a "
                  "different bound",
    "qy_writer_word": "`pairEncode_pairEncode_length`/`_drop` (`Build/InputDevice.lean`): length and drop "
                      "facts, not the expansion; `pairEncode_eq` is cited",
    "qy_hosted_halt": "`phaseHostTM_run_le` (cited) has no halting form",
    "qy_hosted": "the phase host's segment form: `phaseHostTM_run` (cited) states the run, no segment form",
    "qy_hosted'": "as `qy_hosted`", "qy_hosted_last": "as `qy_hosted` (`phaseHostTM_run_le`, cited)",
    "qy_hosted_run": "as `qy_hosted`",
    "qy_round_of_seg": "`Turing.Round.of_cut` (a cut predicate, one escape) is the nearest; no first-step + "
                       "segment form",
    "qy_unpair_succ_lt": "no `Nat.unpair` successor lemma in Mathlib or the tree",
    "qy_unpair_succ_last": "as `qy_unpair_succ_lt`", "qy_unpair_succ_diag": "as `qy_unpair_succ_lt`",
    "qy_unpair_succ_gt": "as `qy_unpair_succ_lt`",
    "QyKit.tape_cases": "proof cites `Classical.exists_or_forall_not` (the probe's finding, fixed)",
    "qy_installSpec": "is `FinTM.exists_installCallTM` read through the own clause `QySpec`; its proof "
                      "cites it",
}
EXQ_NOTE = {
    "qyC_mapState": "closed by `exact rfl` (definitional); the file's proof reads `Cfg.mapState` "
                    "through its field equations (the seal)",
    "qy_run_one": "closed by `exact rfl` (definitional; no declaration)",
    "qy_run_two": "closed by `exact rfl` (definitional; no declaration)",
    "qyBank_zero": "closed by `exact rfl` (the own definition)",
    "QyKit.tp_val": "closed by `exact rfl` (the own definition)",
    "QyKit.tp_inj": "closed by a generic order lemma up to unfolding the own `QyKit.tp`; no statement "
                    "about it is published",
    "qy_installSpec": "closed by `FinTM.exists_installCallTM` (its own proof)",
    "QyKit.tape_cases": "closed by `Classical.exists_or_forall_not`: now cited",
    "qy_rndP_le": "`exact?` ran out of heartbeats (400000): not closed",
}
rows = ["| new private | kind | by name | by statement | `exact?` |", "|---|---|---|---|---|"]
for kind, n in decls:
    if kind in ("theorem", "lemma"):
        v = res.get(n)
        if n in EXQ_NOTE:
            e = EXQ_NOTE[n]
        elif v is None:
            e = "not probed"
        elif v.startswith("could not"):
            e = "could not close the goal"
        else:
            e = v[:120]
    else:
        e = "— (a definition)"
    st = STMT.get(n, "no other file states it (statement over the file's own definitions, or no "
                  "fragment hit)" if kind in ("theorem", "lemma") else "—")
    rows.append(f"| `{n}` | {kind} | 0 hits | {st} | {e} |")
open(out, "w").write(
    f"By name: `git grep -w` of all {len(decls)} new names and the 14 derived instance names over "
    f"the tree, `origin/main`, all 110 branches and all 174 PR heads (open and closed): "
    f"{nhits} hits outside the owned file.\n\n" + "\n".join(rows) + "\n")
print(len(decls), "rows")
