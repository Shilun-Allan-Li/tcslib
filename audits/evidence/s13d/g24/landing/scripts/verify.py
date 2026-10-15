"""Verify the §13d G2–G4 landing's logs against the expectations the gate established, fail-closed.

Usage: python3 -I verify.py <landing folder L> <gate folder G>

Reads the logs that scripts/logs.sh and scripts/screens3.sh wrote in L, and the gate's logs in G
for the results that must carry over unchanged (the unit's, probe and zone-chain axiom prints, the
new Catalog prints, the accepted screen delta). Every check is a function from log text to a list
of failures; the checker controls at the end feed each check a deliberately broken input and
require it to fail. Writes nothing; prints one PASS/FAIL line per check; exit 1 on any failure.
"""
import os
import re
import sys

L, G = sys.argv[1:3]
STD = {"propext", "Classical.choice", "Quot.sound"}


def rd(p):
    return open(p, encoding="utf-8").read()


# ------------------------------------------------------------------ parsers
def entries(text):
    """The `* `label`` entries of a cut-check style log: label, exit, errors, sorried set."""
    out, cur = [], None
    for line in text.split("\n"):
        if line.startswith("* "):
            cur = {"label": line, "exit": None, "errors": None, "sorried": None, "nsorry": None}
            out.append(cur)
        elif cur is not None:
            m = re.match(r"\s+exit (\d+) \| errors (\d+) \|", line)
            if m and cur["exit"] is None:
                cur["exit"], cur["errors"] = int(m.group(1)), int(m.group(2))
                cur["nsorry"] = int(re.search(r"`declaration uses 'sorry'` (\d+)", line).group(1))
            m = re.match(r"\s+sorried:(.*)$", line)
            if m and cur["sorried"] is None:
                cur["sorried"] = set(m.group(1).split())
    return out


def find(es, key):
    hit = [e for e in es if key in e["label"]]
    return hit[0] if len(hit) == 1 else None


def axiom_lines(text):
    """(name, axioms) for every `#print axioms` result line."""
    out = []
    for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text):
        out.append((m.group(1), frozenset(a.strip() for a in m.group(2).split(",") if a.strip())))
    for m in re.finditer(r"'([^']+)' does not depend on any axioms", text):
        out.append((m.group(1), frozenset()))
    return out


def section(text, start, end=None):
    i = text.index(start)
    j = text.index(end, i + len(start)) if end else len(text)
    return text[i:j]


# ------------------------------------------------------------------ checks
UNIT6 = {"zoneCascadeRight_frame", "zoneCascadeRight_home", "copyMapTM_run_ofCfg",
         "transferMapTM_run_ofCfg", "exists_zoneRebalanceTM", "exists_zoneExtendTM"}
CAT2 = {"copyMapTM_run_ofCfg", "transferMapTM_run_ofCfg"}
FR, HO = "zoneCascadeRight_frame", "zoneCascadeRight_home"
CUTS = {"Build.Catalog.part1.check": set(), "Build.Catalog.part2.check": CAT2,
        "Build.Contract.Catalog.part3.check": set(), "Build.Contract.Catalog.part4.check": CAT2,
        "Build.Zone.check": {FR, HO},
        "Build.ZoneRebalance.check": {FR, HO, "exists_zoneRebalanceTM", "exists_zoneExtendTM"},
        "Build.ZoneTape.check": {FR, HO}}
LANDED = {"landed/.../Build/Zone.lean": {HO},
          "work/LandedChain.lean": {HO, "exists_zoneRebalanceTM", "exists_zoneExtendTM"},
          "landed/.../Build/Catalog.lean": CAT2, "work/CatChain.lean": CAT2}


def check_cuts(text):
    es, f = entries(text), []
    for key, want in list(CUTS.items()) + list(LANDED.items()):
        e = find(es, key)
        if e is None:
            f.append(f"{key}: entry missing or ambiguous")
        elif e["exit"] != 0 or e["errors"] != 0 or e["sorried"] != want:
            f.append(f"{key}: exit {e['exit']} errors {e['errors']} sorried {sorted(e['sorried'] or [])}")
    for key, n in (("baseline: the base's `Build/Catalog.lean`", 0), ("baseline: the base's `Build/Zone.lean`", 2)):
        e = find(es, key)
        if e is None or e["exit"] != 0 or e["errors"] != 0 or e["nsorry"] != n:
            f.append(f"{key}: {e}")
    m = re.search(r"warnings of the landed file minus the baseline's.*?\n((?:    [<>].*\n)*)", text)
    lines = [l for l in (m.group(1).split("\n") if m else []) if l.strip()]
    if len(lines) != 2 or not all(l.strip().startswith(">") and "declaration uses 'sorry'" in l for l in lines):
        f.append(f"landed Catalog warnings minus the baseline's: {lines}")
    if "warnings minus the base Catalog's: 2 lines" not in text:
        f.append("CatChain warnings minus the base Catalog's is not exactly the 2 sorries")
    return f


FREEZE = {
    "Build/Catalog.lean": ({"Turing.transferTM", "Turing.copyTM", "Turing.catalog_copy_forward",
                            "Turing.catalog_copy_trace", "Turing.catalog_transfer_trace"},
                           ["Turing.copyMapTM", "Turing.transferMapTM", "Turing.copyMapTM_plain",
                            "Turing.transferMapTM_plain", "Turing.copyMapTM_run_ofCfg",
                            "Turing.transferMapTM_run_ofCfg"]),
    "Build/Contract/Catalog.lean": ({"Turing.clearTM_contract", "Turing.clearTM_contract_frames",
                                     "Turing.clearTM_contract_traj"},
                                    ["Turing.sweepPost", "Turing.sweepContract", "Turing.sweepContract_traj",
                                     "Turing.sweep_ite_keep", "Turing.sweepMapWrite",
                                     "Turing.copyMapTM_contract", "Turing.transferMapTM_contract",
                                     "Turing.copyMapTM_contract_frames",
                                     "Turing.transferMapTM_contract_frames",
                                     "Turing.copyMapTM_contract_traj"])}


def check_freeze(text):
    f = []
    for name, (bodies, added) in FREEZE.items():
        blk = section(text, f"## `{name}`", "```\n\n")
        got = {l.split()[1] for l in blk.split("\n") if l.startswith(("BODY", "STATEMENT", "REMOVED", "SIG"))}
        kinds = {l.split()[0] for l in blk.split("\n") if l.startswith(("BODY", "STATEMENT", "REMOVED", "SIG"))}
        if got != bodies or kinds != {"BODY"}:
            f.append(f"{name}: changed declarations {sorted(got)} kinds {sorted(kinds)}")
        m = re.search(r"(\d+) old declarations: identical (\d+), statement changed (\d+), body changed (\d+), "
                      r"removed (\d+); added (\d+): (.*)", blk)
        if not m:
            f.append(f"{name}: no summary line")
            continue
        old, ident, sc, bc, rem, na, names = m.groups()
        if int(sc) or int(rem) or int(bc) != len(bodies) or int(ident) != int(old) - len(bodies):
            f.append(f"{name}: summary {m.group(0)[:120]}")
        if [n.strip() for n in names.split(",")] != added:
            f.append(f"{name}: added {names[:200]}")
    dn = section(text, "of which name the definitions inside", "kinds of the other lines")
    if [l.strip() for l in dn.split("\n")[1:] if l.strip()] != ["(none)"]:
        f.append("a downstream proof unfolds copyTM/transferTM/clearTM_contract by name")
    return f


def check_axioms(text, cat_before, cat_after, gate_text):
    f = []
    allp = axiom_lines(text) + axiom_lines(cat_before) + axiom_lines(cat_after)
    bad = sorted({(n, tuple(sorted(a - STD - {"sorryAx"}))) for n, a in allp if a - STD - {"sorryAx"}})
    if bad:
        f.append(f"axioms outside the standard three and sorryAx: {bad[:5]}")
    if not allp:
        f.append("no axiom prints parsed")
    head = text.split("## The restructured")[0]
    ghead = gate_text.split("## The restructured")[0]
    if sorted(axiom_lines(head)) != sorted(axiom_lines(ghead)):
        a, b = set(axiom_lines(head)), set(axiom_lines(ghead))
        f.append(f"unit/fit/zone-chain prints differ from the gate's: landing-only {sorted(a - b)[:4]}, "
                 f"gate-only {sorted(b - a)[:4]}")
    m = re.search(r"before (\d+) prints, after (\d+); unchanged (\d+), changed (\d+), missing after (\d+)", text)
    if not m or int(m.group(3)) != int(m.group(1)) or int(m.group(4)) or int(m.group(5)):
        f.append(f"Catalog before/after: {m.group(0) if m else 'no summary'}")
    if "declarations that gain sorryAx: 0" not in text:
        f.append("a Catalog declaration gains sorryAx")
    new = re.findall(r"^  NEW .*$", text, re.M)
    gnew = re.findall(r"^  NEW .*$", gate_text, re.M)
    if new != gnew:
        f.append(f"the new Catalog prints differ from the gate's: {sorted(set(new) ^ set(gnew))[:4]}")
    fr = [a for n, a in axiom_lines(head) if n == "Turing.zoneCascadeRight_frame"]
    if not fr or any("sorryAx" in a for a in fr[-1:]):
        f.append("the promoted zoneCascadeRight_frame is not proved in the landed chain")
    return f


def check_names(text):
    f = []
    unit = text.split("Positive control")[0]
    clashes = re.findall(r"CLASH (\S+)", unit)
    if clashes != ["Turing.zoneCascadeRight_frame"]:
        f.append(f"full-name clashes {clashes} (expected only the promotion)")
    for m in re.finditer(r"2\. shared with (\S+): (\d+)", unit):
        if int(m.group(2)):
            f.append(f"shares {m.group(2)} names with {m.group(1)}")
    if len(re.findall(r"2\. shared with", unit)) != 8:
        f.append("not all 8 statement units were screened")
    if "4. duplicates within the unit: []" not in unit:
        f.append("duplicates within the unit")
    ctrl = text.split("Positive control")[1]
    if sorted(re.findall(r"CLASH (\S+)", ctrl)) != ["Turing.zoneBase_succ", "Turing.zoneSide"]:
        f.append("the positive control did not catch its 2 planted clashes")
    return f


RETIRED = ["zoneCellBits", "zoneCellOf", "zoneCellOf_bits", "zoneTape", "zoneTape_empty",
           "zoneTape_blank_outside", "zoneTape_homeWrite", "zoneStageWord", "zoneStageWord_length",
           "zoneStageWord_getElem", "zoneStageSlot", "zoneStage_rightWindow", "zoneStage_leftWindow",
           "zoneStage_window_bounds", "exists_zoneShiftInTM", "exists_zoneShiftOutTM"]


def check_retire(text):
    f = []
    for n in RETIRED:
        m = re.search(rf"^{re.escape(n)}\s+Lean consumers outside Zone: (.*?) \|", text, re.M)
        if not m or m.group(1) != "none":
            f.append(f"{n}: {m.group(1) if m else 'missing'}")
    return f


def check_elab(text, gate_text):
    f = []
    es = entries(text.replace("### G24Statements.lean", "* `G24Statements.lean`"))
    u = find(es, "G24Statements.lean")
    if u is None or u["exit"] != 0 or u["errors"] != 0 or u["sorried"] != UNIT6:
        f.append(f"unit: {u}")
    for n in ("neg1", "neg2", "neg3", "neg4"):
        m = re.search(rf"^\* `{n}`: exit (\d+), errors (\d+)", text, re.M)
        if not m or int(m.group(1)) == 0 or int(m.group(2)) < 1:
            f.append(f"{n} did not fail")
    for key in ("probes/G24Sanity.lean", "probes/G24FitProbe.lean"):
        blk = section(text, f"### {key}", "```")
        m = re.search(r"exit (\d+) \| errors (\d+)", blk)
        if not m or m.group(1) != "0" or m.group(2) != "0":
            f.append(f"{key}: {m.group(0) if m else 'no summary'}")
    lint = section(text, "## 5. Style lint", "## 6.")
    glint = section(gate_text, "## 5. Style lint", "## 6.")
    fails = re.findall(r"^FAIL\s+(\S+)\s+(.*)$", lint, re.M)
    if fails != re.findall(r"^FAIL\s+(\S+)\s+(.*)$", glint, re.M):
        f.append(f"campaign lint FAILs differ from the gate's: {fails}")
    tail = lint.split("on the four zone and contract files:")[1]
    finds = [l for l in tail.split("\n") if l.startswith("TCSlib/")]
    if [re.sub(r"\d+ lines", "N lines", l) for l in finds] != \
            ["TCSlib/Complexity/TuringMachine/Build/Zone.lean: N lines (> 1000, must split)"]:
        f.append(f"style_lint findings on the four files: {finds}")
    w = section(text, "## 6. Line widths", "## 7.")
    if "over-100 lines: 0\n" not in w:
        f.append("new material has lines over 100 characters")
    m = re.search(r"\(landed Build/Catalog\.lean: over-100 lines: (\d+); the base's: over-100 lines: (\d+)\)", w)
    if not m or m.group(1) != m.group(2):
        f.append(f"landed Catalog adds over-100 lines: {m.group(0) if m else 'no line'}")
    cite = section(text, "those that do not resolve:", "## 8.")
    gcite = section(gate_text, "those that do not resolve:", "## 8.")
    if " ".join(cite.split()) != " ".join(gcite.split()):
        f.append("the unresolved cited tokens differ from the gate's")
    if "IDENTICAL to the private lemma's" not in text:
        f.append("the promoted zoneCascadeRight_frame's statement differs from the private lemma's")
    return f


def base_label(s):
    # v3 labels a declaration by its full path when two screened files share a basename (here
    # Build/Catalog.lean and Build/Contract/Catalog.lean); the gate's v2 screen used basenames
    path, name = s.split("::", 1)
    return os.path.basename(path) + "::" + name


def pairset(text, kind):
    if kind == "new":
        ps = re.findall(r"^\s+in-file (\S+) <- (\S+) ", text, re.M) + \
             re.findall(r"^\s+CROSS (\S+) <- (\S+) ", text, re.M)
    else:
        ps = re.findall(r"^\s+GONE\s+(\S+)\s+reproduces\s+(\S+):", text, re.M)
    return {(base_label(a), base_label(b)) for a, b in ps}


def check_screens(delta, gate_after):
    f = []
    gd = gate_after.split("## Delta against")[1]
    if pairset(delta, "new") != pairset(gd, "new"):
        f.append(f"new pairs differ from the gate's accepted 24: "
                 f"{sorted(pairset(delta, 'new') ^ pairset(gd, 'new'))[:6]}")
    if pairset(delta, "gone") != pairset(gd, "gone"):
        f.append(f"removed pairs differ from the gate's 7: {sorted(pairset(delta, 'gone') ^ pairset(gd, 'gone'))[:6]}")
    if "(cross-file 0)" not in delta:
        f.append("a new cross-file pair")
    return f


# ------------------------------------------------------------------ run
def run():
    lg = {n: rd(os.path.join(L, f"{n}.log")) for n in ("cutcheck", "freeze", "axioms", "names", "retire", "elaboration")}
    glg = {n: rd(os.path.join(G, f"{n}.log")) for n in ("axioms", "elaboration")}
    cb, ca = rd(os.path.join(L, "work/AxCatBase.out")), rd(os.path.join(L, "work/AxCatAfter.out"))
    delta, gafter = rd(os.path.join(L, "logs/screen-delta.log")), rd(os.path.join(G, "screen-after.txt"))
    checks = [
        ("cut checks and landed forms (7 cuts; Zone, the zone chain, Catalog, the Catalog chain; "
         "sorries exactly at the fill targets)", lambda: check_cuts(lg["cutcheck"])),
        ("freeze: no statement changed, the 5 and 3 listed bodies, the 6 and 10 listed additions; "
         "no downstream unfold of the tables", lambda: check_freeze(lg["freeze"])),
        ("axioms: none beyond the standard three and sorryAx; unit, probe and zone-chain prints equal "
         "the gate's; every Catalog public unchanged, none gains sorryAx; the promotion proved",
         lambda: check_axioms(lg["axioms"], cb, ca, glg["axioms"])),
        ("names: the only full-name clash is the promotion; 8 statement units screened; the positive "
         "control caught 2 of 2", lambda: check_names(lg["names"])),
        ("retirements: the 16 retired names have no Lean consumer outside Zone at the tip",
         lambda: check_retire(lg["retire"])),
        ("unit, probes, the 4 Lean negative controls, lint, widths, citations, the promotion's statement",
         lambda: check_elab(lg["elaboration"], glg["elaboration"])),
        ("copy-text screen (v3): new and removed pairs exactly the gate's accepted 24 and 7, none cross-file",
         lambda: check_screens(delta, gafter)),
    ]
    bad = 0
    for i, (name, fn) in enumerate(checks, 1):
        fs = fn()
        print(f"{'PASS' if not fs else 'FAIL'} {i}: {name}")
        for x in fs:
            print(f"    {x}")
        bad += bool(fs)
    # checker controls: each check must fail on a broken input
    ctl = [
        ("cut checks: an extra sorried declaration",
         lambda: check_cuts(lg["cutcheck"].replace("sorried: zoneCascadeRight_home \n", "sorried: zoneCascadeRight_home extra \n", 1))),
        ("freeze: a changed statement",
         lambda: check_freeze(lg["freeze"].replace("statement changed 0", "statement changed 1", 1))),
        ("freeze: a downstream unfold",
         lambda: check_freeze(lg["freeze"].replace("  (none)\n", "  X.lean:1: simp [copyTM]\n", 1))),
        ("axioms: a foreign axiom",
         lambda: check_axioms(lg["axioms"] + "\n'Turing.x' depends on axioms: [propext, Foo.bar]\n", cb, ca, glg["axioms"])),
        ("names: a second clash",
         lambda: check_names(lg["names"].replace("CLASH Turing.zoneCascadeRight_frame", "CLASH Turing.zoneCascadeRight_frame\n   CLASH Turing.other", 1))),
        ("retirements: a consumer",
         lambda: check_retire(lg["retire"].replace("Lean consumers outside Zone: none", "Lean consumers outside Zone: X.lean", 1))),
        ("unit: a sorry fewer",
         lambda: check_elab(lg["elaboration"].replace(" exists_zoneExtendTM \n", " \n", 1), glg["elaboration"])),
        ("screens: an extra new pair",
         lambda: check_screens(delta + "\n   in-file Zone.lean::a <- Zone.lean::b 99/100 99%\n", gafter)),
    ]
    for i, (name, fn) in enumerate(ctl, 1):
        caught = bool(fn())
        print(f"{'PASS' if caught else 'FAIL'} control {i}: {name} {'is caught' if caught else 'is NOT caught'}")
        bad += not caught
    print(f"TOTAL: {len(checks)} checks and {len(ctl)} checker controls; failures {bad}")
    sys.exit(1 if bad else 0)


run()
