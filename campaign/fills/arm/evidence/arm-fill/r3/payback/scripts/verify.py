"""Fail-closed verdict over every check of the dedup payback landing (read-only; stdlib only).

Usage: python3 -I -B verify.py <S> <L> <base export> <olean snapshot> <packages worktree>
Reads the run's outputs (logs/, work/, tree/, patches/, replay-order.txt, ledger-map.md) and
asserts each criterion. Prints one PASS/FAIL line per check and exits 1 if any fails.
"""
import collections
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import lib  # noqa: E402
import edits as E  # noqa: E402
import cuts  # noqa: E402

S, L, B, OL, WT = sys.argv[1:6]
W, LG = os.path.join(L, "work"), os.path.join(L, "logs")
O = os.path.join(W, "out")
TMP = os.path.join(W, "tmp-scan")
RES = []
STD = {"propext", "Classical.choice", "Quot.sound"}


def rd(p):
    return lib.rd(p)


def check(name, ok, detail=""):
    RES.append(bool(ok))
    print(("PASS " if ok else "FAIL ") + name + (f" — {detail}" if detail else ""))


ENTRY = re.compile(r"^(.*?):(\d+):(\d+): (warning|error)(?:\([^)]*\))?: ", re.M)


def entries(text):
    ms = list(ENTRY.finditer(text))
    res = []
    for i, m in enumerate(ms):
        end = ms[i + 1].start() if i + 1 < len(ms) else len(text)
        msg = text[m.end():end]
        msg = re.split(r"\n(?='[^']+' depends on axioms|'[^']+' does not depend)", msg)[0]
        res.append({"line": int(m.group(2)), "kind": m.group(4),
                    "msg": msg.split("\n\nHint:")[0].strip()})
    return res


def elab(name):
    t = rd(os.path.join(O, name + ".out"))
    es = entries(t)
    return {"exit": int(rd(os.path.join(O, name + ".exit")).strip()), "text": t, "entries": es,
            "errors": [e for e in es if e["kind"] == "error"],
            "sorry": [e for e in es if e["kind"] == "warning" and e["msg"] == "declaration uses 'sorry'"],
            "other": [e for e in es if e["kind"] == "warning" and e["msg"] != "declaration uses 'sorry'"]}


def axioms(text):
    got = dict(re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", text, re.M))
    got.update({n: "" for n in re.findall(r"^'([^']+)' does not depend on any axioms", text, re.M)})
    return {re.sub(r"^_private\.[^.]+\.\d+\.", "", k): {a.strip() for a in v.split(",") if a.strip()}
            for k, v in got.items()}


def decl_at(text, line):
    """The declaration (as written) whose span contains `line` (1-based) of `text`."""
    ds, _ = lib.scan_text(text, TMP)
    for d in ds:
        if d["line"] <= line <= d["end"]:
            return d["name"]
    return None


# ------------------------------------------------------------------ 0. inputs and environment
tip0 = rd(os.path.join(W, "tip-at-start.txt")).strip()
bc = lib.base_commit()
live = lib.tip()
snap = lib.git("rev-parse", "--verify", lib.SNAP_BASE + "^{commit}").strip()
touched = {rel for rel, _, _ in E.FILES.values()}
check(f"base: the export is the given revision (git rev-parse), with the Lean files of the "
      f"snapshot's base {lib.SNAP_BASE}, and the live tip changes none of the touched files",
      bc == tip0 and not lib.lean_diff(bc, snap) and not set(lib.lean_diff(bc, live)) & touched,
      f"export {bc}; live tip {live}; Lean files the tip changed since: {lib.lean_diff(bc, live)}")
pre = subprocess.run([sys.executable, "-I", "-B", os.path.join(HERE, "precheck.py"), S, B, OL, WT, L],
                     capture_output=True, text=True)
check("source precheck: every source present and byte-identical to its tip blob", pre.returncode == 0,
      pre.stdout.strip()[:300])
NC = os.path.join(W, "negctl")
pe, le = rd(os.path.join(NC, "precheck.exit")).strip(), rd(os.path.join(NC, "land.exit")).strip()
check("precheck negative control: without Codec/Word.lean, precheck.py and land.py exit 2 and "
      "write nothing", pe == "2" and le == "2" and "Codec/Word.lean" in rd(os.path.join(NC, "land.out"))
      and rd(os.path.join(NC, "out-exists.txt")).strip() == "absent"
      and rd(os.path.join(NC, "files.txt")).strip() == "unchanged",
      f"exits {pe}/{le}; output {rd(os.path.join(NC, 'out-exists.txt')).strip()}; files of <L> "
      f"{rd(os.path.join(NC, 'files.txt')).strip()}")
sb, sa = rd(os.path.join(W, "repo-status-before.txt")), rd(os.path.join(W, "repo-status-after.txt"))
tb = [l for l in sb.split("\n") if l and not l.startswith("??")]
ta = [l for l in sa.split("\n") if l and not l.startswith("??")]
new_untracked = sorted(set(l for l in sa.split("\n") if l.startswith("??")) -
                       set(l for l in sb.split("\n") if l.startswith("??")))
check("repository untouched: tracked status identical before and after the run; no new untracked "
      "path under TCSlib/ or scripts/ (other sessions share the working tree)",
      tb == ta and not [l for l in new_untracked if l[3:].startswith(("TCSlib/", "scripts/"))],
      f"tracked status lines {len(tb)} = {len(ta)}; new untracked paths (other sessions): "
      f"{[l[3:] for l in new_untracked]}")
# ------------------------------------------------------------------ 1. patches
lo = rd(os.path.join(LG, "land-edits.txt"))
n = len(E.FILES)
check(f"patches: {n} patches replay byte for byte from the tip", lo.count("; replay identical") == n
      and "DIFFERENT" not in lo)
check("comment-only files keep their code (comment-stripped identity, asserted by land.py)",
      lo.count("code unchanged (comment-stripped identity") ==
      sum(1 for v in E.FILES.values() if v[2] == "comment"))
# ------------------------------------------------------------------ 2. elaboration
meta = json.loads(rd(os.path.join(W, "cut", "cuts.json")))
names = json.loads(rd(os.path.join(W, "probes", "names.json")))


def baseline(mod):
    for k, (rel, _, _) in E.FILES.items():
        if lib.mod_of_path(rel) == mod:
            return elab(f"AxBase{k}.lean")
    return elab(f"Base{mod.split('.', 2)[-1].replace('.', '_')}.lean")


base_ok = []
sorry_acct = []
for key, m in meta.items():
    e = elab(f"Ax{key}.lean")
    cut = rd(os.path.join(W, "cut", m["file"]))
    regions_ok, detail = True, []
    for r in m["regions"]:
        ws = [x for x in e["entries"] if r["start"] <= x["line"] <= r["end"]]
        if r["kind"] == "delta":
            if ws:
                regions_ok = False; detail.append(f"delta {r['module']}: {len(ws)} messages")
            continue
        b = baseline(r["module"])
        base_ok.append((r["module"], b["exit"] == 0 and not b["errors"]))
        lw = collections.Counter(x["msg"] for x in ws if x["kind"] == "warning")
        bw = collections.Counter(x["msg"] for x in b["entries"] if x["kind"] == "warning")
        if not r["changed"]:
            if lw != bw:
                regions_ok = False; detail.append(f"{r['module']}: warnings differ from the base")
        else:
            if lw - bw:
                regions_ok = False; detail.append(f"{r['module']}: new warnings {list((lw - bw).elements())[:3]}")
            gone = bw - lw
            if r["module"] == m["module"]:
                rel = lib.path_of_mod(r["module"])
                bt = rd(os.path.join(B, rel))
                lt = rd(os.path.join(L, "tree", rel))
                bs = [decl_at(bt, x["line"]) for x in b["sorry"]]
                ls_ = [decl_at(cut, x["line"]) for x in e["sorry"] if r["start"] <= x["line"] <= r["end"]]
                ds, _ = lib.scan_text(lt, TMP)
                kept = {d["name"] for d in ds}
                lost = sorted(n for n in bs if n not in ls_)
                unexplained = [n for n in lost if n in kept]
                sorry_acct.append((key, len(bs), len(ls_), lost))
                if unexplained or len(ls_) > len(bs):
                    regions_ok = False; detail.append(f"{key}: sorry {len(bs)} -> {len(ls_)}, {unexplained}")
                if gone - collections.Counter({"declaration uses 'sorry'": len(lost)}):
                    regions_ok = False
                    detail.append(f"{key}: warnings gone beyond deleted sorries "
                                  f"{list((gone - collections.Counter({'declaration uses ' + chr(39) + 'sorry' + chr(39): len(lost)})).elements())[:3]}")
    ok = (e["exit"] == 0 and not e["errors"] and len(e["sorry"]) == m["expected_sorry"] and regions_ok)
    check(f"elaboration {key}: {m['lines']} lines, {len(m['inlined'])} inlined, deltas "
          f"{[d.split('.')[-1] for d in m['deltas']]}: exit 0, 0 errors, sorry = expected, no new "
          f"warning", ok, f"exit {e['exit']}, errors {len(e['errors'])}, sorry {len(e['sorry'])} "
          f"(expected {m['expected_sorry']}), other warnings {len(e['other'])}"
          + (f"; {detail[:3]}" if detail else ""))
check("baselines: every base text used as a warning baseline elaborates against the snapshot",
      all(ok for _, ok in base_ok), sorted({m for m, ok in base_ok if not ok}))
tot_b = sum(a for _, a, _, _ in sorry_acct)
tot_l = sum(b for _, _, b, _ in sorry_acct)
lost = [(k, x) for k, _, _, x in sorry_acct if x]
check("sorry counts unchanged except deleted sorried declarations (each accounted for)",
      all(b - c == len(x) for _, b, c, x in sorry_acct),
      f"changed modules: {tot_b} sorried declarations at the base, {tot_l} landed; deleted sorried: "
      f"{lost if lost else 'none'}")
# ------------------------------------------------------------------ 3. axioms
bad_ax, new_sorry, counted = [], [], 0
for key in E.FILES:
    if key not in meta or f"Ax{key}" not in names:
        continue
    la = axioms(elab(f"Ax{key}.lean")["text"])
    ba = axioms(elab(f"AxBase{key}.lean")["text"])
    for nm in names[f"Ax{key}"]:
        if nm not in la:
            bad_ax.append(f"{key}: no print for {nm}")
            continue
        counted += 1
        ax = la[nm]
        allowed = STD | ({"sorryAx"} if "sorryAx" in ba.get(nm, set()) else set())
        if ax - allowed:
            (new_sorry if "sorryAx" in ax - allowed else bad_ax).append(f"{key}: {nm} {sorted(ax)}")
check("axioms: every landed declaration of the touched files depends on the standard three only, "
      "plus sorryAx where its base version already did", not bad_ax and not new_sorry,
      f"{counted} declarations printed; new sorryAx {new_sorry[:3]}; other {bad_ax[:3]}")
# ------------------------------------------------------------------ 4. negative controls
for nme, why in (("NegDirect.lean", "error"), ("NegMutant.lean", "error"), ("NegNoDelta.lean", "arm_chain")):
    e = elab(nme)
    errs = [x["msg"] for x in e["errors"]]
    check(f"negative control {nme[:-5]} FAILS", e["exit"] != 0 and errs and
          (why == "error" or any(why in x for x in errs)),
          f"exit {e['exit']}, {len(errs)} errors; first: {errs[0][:100] if errs else ''!r}")
fb, fl = elab("FacadeFullBase.lean"), elab("FacadeFullLanded.lean")
mb = collections.Counter(x["msg"] for x in fb["errors"])
ml = collections.Counter(x["msg"] for x in fl["errors"])
check("artifact control: the facade's 38-module cut fails identically for the base and the landed "
      "texts (`Mem`), so it is no evidence about the landing", fb["exit"] != 0 and fl["exit"] != 0
      and mb == ml and any("Mem" in x for x in mb),
      f"base {sum(mb.values())} errors, landed {sum(ml.values())}; same messages: {mb == ml}")
# ------------------------------------------------------------------ 5. freeze, API delta, controls
fz = rd(os.path.join(LG, "freeze.log"))
check(f"freeze: the {n} files PASS (every difference authorized; every allowance used)",
      fz.count("RESULT: PASS") == n and "OVERALL: PASS" in fz)
delta = json.loads(rd(os.path.join(W, "api-delta.json")))
pr = sum(len(v["public_removed"]) for v in delta.values())
check("public removals are exactly the deleted copies and moves (in Hydroxyi's files)", pr == 7 and
      all(set(v["public_removed"]) <= {nm for nm, _ in E.DELETED.get(k, set())} for k, v in delta.items()),
      f"{pr}: " + ", ".join(x for v in delta.values() for x in v["public_removed"]))
ct = rd(os.path.join(LG, "controls.log"))
check("freeze controls C1-C9 and the name control each FAIL", "controls: 10; failing as required: 10" in ct)
# ------------------------------------------------------------------ 6. names, hygiene, lint
nm = rd(os.path.join(LG, "names.log"))
check("names: 0 full-name clashes", "clashes: 0" in nm)
check("names: no stale use of a deleted declaration in the landed tree", "; stale uses: 0" in nm)
check("names: the new import of VWord adds no clash and no `open List` downstream",
      "full-name clashes []; downstream files opening List: []" in nm)
check("names: no added line refers to another file's private declaration", "references: []" in nm)
hy = rd(os.path.join(LG, "hygiene.log"))
check("widths: every added line at most 100 columns", hy.count("over 100: 0") == n)
check("hygiene: no #eval/run_cmd/IO/unsafe/implemented_by/extern/native_decide/syntax/macro/elab "
      "in added lines", "base file; hits: []" in hy)
check("cut identity: inlined regions and deltas are the landed texts; probes begin with their cuts",
      "RESULT: PASS" in hy)
lb = rd(os.path.join(W, "lint", "base.out")).split("\n")
ll = rd(os.path.join(W, "lint", "land.out")).split("\n")
nf = lambda ls: sorted(re.sub(r"line \d+", "line N", l) for l in ls if l.startswith("FAIL"))
check("lint: the base's campaign_style_lint.py gives no new FAIL", not (collections.Counter(nf(ll)) -
      collections.Counter(nf(lb))), f"{len(nf(lb))} FAIL lines at the base, {len(nf(ll))} landed")
wb = collections.Counter(l for l in lb if l.startswith("WARN"))
wl = collections.Counter(l for l in ll if l.startswith("WARN"))
norm = lambda c: collections.Counter(re.sub(r"\d+ lines", "N lines", l) for l in c.elements())
came = norm(wl - wb) - norm(wb - wl)
check("lint: no new WARN (only the size numbers of touched files change)", not came,
      f"{sum((wl - wb).values())} WARN lines changed; new: {list(came.elements())[:3]}")
# ------------------------------------------------------------------ 7. replay list, ledger, scope
gl = rd(os.path.join(LG, "graph.log"))
rl = rd(os.path.join(L, "replay-order.txt")).split("\n")
assert rl[-1] == ""
rl = rl[:-1]
mm = re.search(r"Replay list: (\d+) modules", gl)
check("replay list: no root TCSlib, no duplicates, every touched module listed, topological, every "
      "import listed or with an olean", "TCSlib" not in rl and len(set(rl)) == len(rl) and
      all(v[0][:-5] in rl for v in E.FILES.values()) and mm and int(mm.group(1)) == len(rl) and
      "imports check: PASS" in gl and "cut imports check: PASS" in gl, f"{len(rl)} modules")
lm = rd(os.path.join(L, "ledger-map.md"))
check("ledger map: every P1, P1+ and manual row and L049 mapped", lm.count("\n| L") + lm.count("\n| S0")
      + lm.count("(manual)") >= 39 and "| L049 |" in lm)
tf = [os.path.relpath(os.path.join(dp, f), os.path.join(L, "tree"))
      for dp, _, fs in os.walk(os.path.join(L, "tree")) for f in fs]
check("CircuitComplexity: only DAGCircuitSat, with exactly its two promotions (D4, as extended)",
      [f for f in tf if "CircuitComplexity/" in f] == [E.FILES["DAGCircuitSat"][0]] and
      delta["DAGCircuitSat"]["promoted"] == ["BoolCircuit.DAGCircuit.eval_tseitinGates_values",
                                             "BoolCircuit.DAGCircuit.values_getD_eq_of_eval_tseitinGates"]
      and not delta["DAGCircuitSat"]["proofs_changed"] and lo.count("make public eval_tseitinGates_values") == 1
      and lo.count("make public values_getD_eq_of_eval_tseitinGates") == 1)
check("in-flight landings: no touched file (MIG-1 S, C1-A round 2, G2-G4)",
      gl.count("touched by this landing: []") == 3)
print(f"\n{sum(RES)}/{len(RES)} checks passed")
print("VERDICT:", "PASS" if all(RES) else "FAIL")
sys.exit(0 if all(RES) else 1)
