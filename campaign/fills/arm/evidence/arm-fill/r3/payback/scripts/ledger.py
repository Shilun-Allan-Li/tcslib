"""The ledger map of the dedup payback landing (read-only; writes <L>/ledger-map.md).

Usage: python3 -I -B ledger.py <base export> <L>

Every pair row of `audits/evidence/arm-fill/r2/classify.tsv` in groups P1 and P1+, the manual
rows of `manual.tsv` in those groups (the three below-floor D rows and M2), and L049 (R2-1),
mapped to this landing's edit: the copy side and the original side, each with its action and
its `file:line` at the base (the campaign tip) and in the landed tree. Rows are read from the
evidence files (asserted complete: every P1/P1+ row has an entry here and vice versa). Lines
are declaration lines (the keyword line), found by the MIG-1 gate's declaration scanner.
"""
import csv
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402

TMP = os.path.join(lib.L, "work", "tmp-scan")
R2 = "audits/evidence/arm-fill/r2/"
SC, CP = "SpaceComplexity/", "ClassPSPACE/"
IA = SC + "Logspace/InputAccess.lean"
CG = SC + "ConfigGraph.lean"
# row -> (copy action, original action, the shared declaration or note)
ACT = {
    "S030": ("re-pointed", "re-pointed", ("arm_chain", IA, "both directions of the new chain lemma")),
    "L001": ("re-pointed", "re-pointed", ("indicator_inputBitLang", IA, "the public bit-oracle answer")),
    "L002": ("re-pointed", "re-pointed (cites `indicator_inputBitLang`, as in L001); its length "
             "sibling `drop_len` now cites `indicator_inputLenLang`: new pair L3-002",
             ("indicator_inputLenLang", IA, "the public length-oracle answer")),
    "L003": ("kept (the single home)", "deleted (D6)", None),
    "L004": ("kept (the single home)", "deleted (D6)", None),
    "L005": ("kept (the single home)", "deleted (D6)", None),
    "L006": ("kept (the single home)", "deleted (D6)", None),
    "L009": ("kept (the single home)", "deleted (D6)", None),
    "L010": ("kept (the single home)", "deleted (D6)", None),
    "L011": ("re-pointed", "kept", ("length_pairEncode_drop_le", "ClassNP/PolyTimeBlockLoop.lean",
                                    "the shared pair-step bound")),
    "L012": ("re-pointed", "re-pointed", ("length_pairEncode_drop_le", "ClassNP/PolyTimeBlockLoop.lean",
                                          "the shared pair-step bound")),
    "L016": ("moved (deleted here)", "kept", ("prefixTruth_congr_agree", "Formulas/QBF.lean",
                                               "moved in, verbatim")),
    "L017": ("moved (deleted here)", "re-pointed (corollary)",
             ("prefixTruth_congr_agree", "Formulas/QBF.lean", "moved in, verbatim")),
    "L024": ("deleted (D4, as extended by the user)", "promoted (D4 exception)", None),
    "L025": ("re-pointed", "promoted (D4 exception)", None),
    "L033": ("kept: deferred to ARM-2 and the dedup window (user)", "kept private", None),
    "L038": ("deleted (D2h)", "promoted", None),
    "L039": ("deleted (D2h)", "promoted", None),
    "L040": ("deleted (D2h)", "promoted", None),
    "L041": ("deleted (D2h)", "promoted", None),
    "L042": ("deleted (D2)", "promoted, restated with Cfg.InWindow (D1)", None),
    "L043": ("deleted (D3)", "re-pointed (backward branch)",
             ("DecidesInSpace.mem_of_acceptsWithin", CG, "the backward branch, factored out")),
    "L045": ("moved (deleted here)", "kept", ("outSummary_eq_empty_iff", CG, "moved beside its sibling")),
    "L046": ("re-pointed", "re-pointed (instance)", ("arm_chain", IA, "up = true")),
    "L047": ("re-pointed", "re-pointed (instance)", ("arm_chain", IA, "up = false")),
    "L048": ("re-pointed", "re-pointed (stride-1 instance)",
             ("boundedDecodeStride_loop", IA, "the stride decoder")),
    "L049": ("re-pointed", "promoted", None),
    "L050": ("re-pointed", "re-pointed", ("pairEncode_getD_snd", IA, "the new index lemma")),
    "L052": ("re-pointed", "re-pointed", ("pairEncode_getD_snd", IA, "the new index lemma")),
    "L054": ("re-pointed", "moved to InputAccess, public", ("drop_canon", IA, "moved down, public")),
    "L055": ("re-pointed", "moved to InputAccess, public", ("drop_canon", IA, "moved down, public")),
    "L056": ("re-pointed", "re-pointed", ("indicator_inputBitLang", IA, "the public bit-oracle answer")),
    "L057": ("re-pointed", "re-pointed (cites `indicator_inputBitLang`, as in L056); its length "
             "sibling `drop_len` now cites `indicator_inputLenLang`: new pair L3-004",
             ("indicator_inputLenLang", IA, "the public length-oracle answer")),
    "L119": ("kept: not real duplication (user)", "kept", None),
    "L120": ("kept: not real duplication (user)", "kept", None),
    "M:InWin": ("deleted (D1)", "deleted (D1; both replaced by Turing.Cfg.InWindow)", None),
    "M:inWin_of_coreSum_eq": ("deleted (D5)", "promoted, restated with Cfg.InWindow (D1)", None),
    "M:synOK": ("kept (the single home)", "deleted (D6)", None),
    "M:getD_drop": ("re-pointed (new import TCSlib.Programs.Util.List)", "kept", None),
}
# R3-2 (ARM gate round 3, 2026-10-15): L002 and L057 keep their pair's original side,
# `drop_bit`; they had been relabelled with its sibling `drop_len`.
ORIG_FOR = {"L017": "prefixTruth_congr",
            "L043": "DecidesInSpace.mem_iff_acceptsWithin_configBound"}


def line_of(root, rel, name):
    p = os.path.join(root, rel)
    if not os.path.isfile(p):
        return None
    ds, _ = lib.scan_text(lib.rd(p), TMP)
    hit = [d["line"] for d in ds if d["name"] == name]
    return hit[0] if len(hit) == 1 else (None if not hit else f"{hit}")


def where(base, tree, rel, name):
    full = "TCSlib/Complexity/" + rel if not rel.startswith("TCSlib/") else rel
    b = line_of(base, full, name)
    t = line_of(tree, full, name) if os.path.isfile(os.path.join(tree, full)) else line_of(base, full, name)
    short = full.replace("TCSlib/Complexity/", "")
    return (f"`{short}:{b}`" if b else "—"), (f"`{short}:{t}`" if t else "—")


def main():
    base, L = sys.argv[1:3]
    tree = os.path.join(L, "tree")
    cls = list(csv.DictReader(open(os.path.join(base, R2 + "classify.tsv"), encoding="utf-8"),
                              delimiter="\t"))
    pairs = {r["pid"]: r for r in csv.DictReader(open(os.path.join(base, R2 + "pairs.tsv"),
                                                      encoding="utf-8"), delimiter="\t")}
    man = [l.split("\t") for l in lib.rd(os.path.join(base, R2 + "manual.tsv")).strip().split("\n")]
    rows = [(r["pid"], r["group"], r["family"]) for r in cls if r["group"] in ("P1", "P1+")]
    rows.append(("L049", "R2-1", "-"))
    want = {p for p, _, _ in rows}
    mrows = [m for m in man if m[4] in ("P1", "P1+")]
    for m in mrows:
        want.add("M:" + m[2])
    assert want == set(ACT), (sorted(want - set(ACT)), sorted(set(ACT) - want))
    out = ["# Ledger map: the payback PR's edit for each P1, P1+ and M2 row, and L049",
           "",
           f"Generated by `scripts/ledger.py` from `{R2}classify.tsv`, `pairs.tsv` and `manual.tsv` "
           f"at the base `{lib.base_commit()}` (the export; LANDING-NOTES.md §0). Lines are declaration lines: "
           "*before* at the base, *after* in the landed tree (— where the declaration is absent). "
           "The ledger's own line numbers are at the received tree `8c23f3bc`.",
           "",
           "*Corrected 2026-10-15 (ARM gate round 3, finding R3-2):* rows L002 and L057 name their "
           "pair's original side, `drop_bit`, as `pairs.tsv` does; the landed map had relabelled it "
           "with the sibling `drop_len`, whose pairs with `orc_len` are the new L3-002 and L3-004. "
           "No other row, classification or total changes.",
           "",
           f"Rows: {len(rows) - 1} pair rows in groups P1 and P1+ ("
           f"{sum(1 for _, g, _ in rows if g == 'P1')} P1, {sum(1 for _, g, _ in rows if g == 'P1+')} "
           f"P1+), {len(mrows)} manual rows ({', '.join(m[0] + ' ' + m[2] for m in mrows)}), and L049.",
           "",
           "| Row | Group, family | Copy side | Copy: action | before | after | Original side | "
           "Original: action | before | after | Shared declaration (after) |",
           "|---|---|---|---|---|---|---|---|---|---|---|"]
    counts = {}
    for pid, grp, fam in rows:
        r = pairs[pid]
        ca, oa, shared = ACT[pid]
        arel, an = r["A_path"], r["A_name"]
        brel, bn = r["B_path"], ORIG_FOR.get(pid, r["B_name"])
        if pid == "S030":
            arel, an, brel, bn = r["A_path"], r["A_name"], r["B_path"], r["B_name"]
        a0, a1 = where(base, tree, arel, an)
        b0, b1 = where(base, tree, brel, bn)
        sh = "—"
        if shared:
            s0, s1 = where(base, tree, shared[1], shared[0])
            sh = f"`{shared[0]}` {s1} ({shared[2]})"
        counts[ca.split(" ")[0].rstrip(":")] = counts.get(ca.split(" ")[0].rstrip(":"), 0) + 1
        out.append(f"| {pid} | {grp}, {fam} | `{an}` | {ca} | {a0} | {a1} | `{bn}` | {oa} | {b0} | "
                   f"{b1} | {sh} |")
    for m in mrows:
        cls_, crel, cname, _, grp = m[:5]
        basis = m[5]
        orig = basis.split("original ")[1].split(",")[0]
        orel, oname = orig.split("::")
        oname = oname.split(" line")[0]
        key = "M:" + cname
        ca, oa, shared = ACT[key]
        a0, a1 = where(base, tree, crel, cname)
        b0, b1 = where(base, tree, orel, oname)
        counts[ca.split(" ")[0].rstrip(":")] = counts.get(ca.split(" ")[0].rstrip(":"), 0) + 1
        out.append(f"| {cls_} (manual) | {grp} | `{cname}` | {ca} | {a0} | {a1} | `{oname}` | {oa} | "
                   f"{b0} | {b1} | {'`Turing.Cfg.InWindow` (`TuringMachine/Build/CfgRecord.lean`, unchanged)' if cname == 'InWin' else '—'} |")
    out += ["", "Copy-side actions: " + ", ".join(f"{k} {v}" for k, v in sorted(counts.items())), "",
            "**Dispositions (user, 2026-10-14; backlog ARM-1):** L024 is done under the extended D4 "
            "exception (the second visibility change in `DAGCircuitSat`); L050 and L052 are re-pointed "
            "to the new `Complexity.pairEncode_getD_snd`; L033 (G-rep, `pt_rep_mul`) is deferred to "
            "ARM-2 and the user's dedup window; L119 and L120 (G-vword) are accepted as not real "
            "duplication. Both stay unchanged.", ""]
    lib.wr(os.path.join(L, "ledger-map.md"), "\n".join(out))
    print(f"ledger-map.md: {len(rows)} pair rows (with L049) and {len(mrows)} manual rows; copy-side "
          f"actions {counts}")


if __name__ == "__main__":
    main()
