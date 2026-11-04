#!/usr/bin/env python3
"""Have hygiene and have→lemma extraction: the driver for `TCSlib/Tactics/Haves.lean`.

The Lean side elaborates one file, reads every tactic `have` off the info trees (its
elaborated type, its proof term, where its name is used, what it depends on, its exact
source range), rewrites the text, and re-elaborates to verify before writing.  This
script runs it per file, keeps the triage manifests of `have2lemma/` in step, and runs
the fixture tests.

    python3 scripts/haves.py scan    FILE [--json]            facts about every have
    python3 scripts/haves.py clean   FILE... [--write]        remove unnecessary haves
    python3 scripts/haves.py extract FILE DECL:HAVE[@LINE]:NAME ... [--write] [--private]
                                                              [--doc TEXT]
    python3 scripts/haves.py census  [DIR|FILE ...]           count removable haves per file
    python3 scripts/haves.py manifest FILE...                 write have2lemma/manifests/<Module>.json
    python3 scripts/haves.py queue   [--write] [--file F]     convert the `queued` manifest entries
    python3 scripts/haves.py test                             run the fixture suite

Without `--write`, `clean` and `extract` print the unified diff of what they would do
and leave the file alone.  Every rewrite is verified by re-elaboration on the Lean side;
a file is written only when no new error appears.  The Lean process runs under
`lake env` so the library's `.olean`s are found; the target file's own imports must be
built (that is `lake build <its module>`), nothing else is compiled.

What `clean` removes (each decided on the proof term, never on the text):

* an **unused** have — its name does not occur in the rest of the proof term;
* **have-then-exact** — `have h : T := p` followed by `exact h` with no other use:
  `p` is inlined, behind `show T` when `T` is not syntactically the goal;
* **rfl-have-then-rw** — `have h : A = B := rfl` whose single use is `rw [h]` on the goal
  `A`: `change B`.

`clean` iterates until nothing changes (a have used only by a deleted have is unused in
the next round).  `extract` turns a have into a declaration before its theorem and
replaces the have's proof by a call, so later uses of the name are untouched; it refuses
haves that depend on inaccessible (`a✝`) or `let`-bound hypotheses.
"""

from __future__ import annotations

import argparse
import difflib
import json
import os
import re
import subprocess
import sys
from datetime import date
from pathlib import Path

BASE = Path(__file__).resolve().parent.parent
DRIVER = BASE / "TCSlib" / "Tactics" / "Haves.lean"
FIXTURES = BASE / "TCSlib" / "Tactics" / "HavesFixtures.lean"
MANIFESTS = BASE / "have2lemma" / "manifests"
QUEUE = BASE / "have2lemma" / "QUEUE.md"
SCRATCH = Path(os.environ.get("HAVES_SCRATCH", BASE / "have2lemma" / ".out"))


def run_driver(cmd: str, file: Path, extra: list[str], quiet: bool = False) -> dict | list:
    """Run the Lean driver; return its JSON report.  stderr is the progress log."""
    argv = ["lake", "env", "lean", "--run", str(DRIVER), cmd, str(file)] + extra
    proc = subprocess.run(argv, cwd=BASE, capture_output=True, text=True)
    if not quiet:
        for line in proc.stderr.splitlines():
            if line.startswith("[haves]"):
                print("   ", line, file=sys.stderr)
    if proc.returncode == 2 or not proc.stdout.strip():
        sys.stderr.write(proc.stderr)
        raise SystemExit(f"haves: the driver failed on {file} (exit {proc.returncode})")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError:
        sys.stderr.write(proc.stdout + proc.stderr)
        raise SystemExit(f"haves: no JSON report from the driver for {file}")


def rel(p: Path) -> str:
    try:
        return str(p.resolve().relative_to(BASE))
    except ValueError:
        return str(p)


def lean_files(paths: list[str]) -> list[Path]:
    out: list[Path] = []
    for p in paths or ["TCSlib"]:
        path = Path(p)
        if path.is_dir():
            out += sorted(path.rglob("*.lean"))
        else:
            out.append(path)
    return [p for p in out if "Tactics" not in p.parts or p.name == "HavesFixtures.lean"]


def show_diff(file: Path, new_path: Path) -> None:
    old = file.read_text().splitlines(keepends=True)
    new = new_path.read_text().splitlines(keepends=True)
    sys.stdout.writelines(difflib.unified_diff(old, new, fromfile=rel(file), tofile=rel(file) + " (rewritten)"))


def print_report(report: dict) -> None:
    for c in report.get("changes", []):
        print(f"  {c['kind']:8} {c['declaration']}.{c['have']} (line {c['line']}): {c['detail']}")
    for c in report.get("skipped", []):
        print(f"  skipped  {c['declaration']}.{c['have']} (line {c['line']}): {c['detail']}")
    for m in report.get("newErrors", []):
        print(f"  NEW ERROR line {m['line']}: {m['text'].splitlines()[0]}")
    for m in report.get("newWarnings", []):
        print(f"  new warning line {m['line']}: {m['text'].splitlines()[0]}")


# ── scan / census / manifest ────────────────────────────────────────────────

def cmd_scan(args) -> int:
    sites = run_driver("scan", Path(args.file), [])
    if args.json:
        print(json.dumps(sites, indent=1, ensure_ascii=False))
        return 0
    for s in sites:
        flags = [k for k in ("unused", "exactAfter", "rflEq", "destructuring") if s.get(k)]
        if s.get("inaccessibleDeps"):
            flags.append("inaccessible-deps")
        if s.get("letDeps"):
            flags.append("let-deps")
        kind = s.get("singleTacticClose") and f"single:{s['singleTacticClose']}" or f"{s['bodyLines']} lines"
        print(f"{s['line']:5}  {s['declaration'].split('.')[-1]}.{s['haveName']:<16} uses={s.get('useCount', '?')}"
              f"  {kind:<14} deps={','.join(s.get('localDeps', []))}  {' '.join(flags)}"
              + (f"  ERROR {s['error']}" if s.get("error") else ""))
    return 0


def removable(site: dict) -> str | None:
    if site.get("destructuring") or site.get("error") or site.get("hintOnly"):
        return None
    if site.get("unused"):
        return "unused"
    if site.get("exactAfter"):
        return "exact"
    if site.get("rflEq") and site.get("nextTactic") == "rw" and site.get("useCount") == 1:
        return "rfl-rw"
    return None


def cmd_census(args) -> int:
    files = lean_files(args.paths)
    total = {"haves": 0, "unused": 0, "exact": 0, "rfl-rw": 0}
    rows = []
    for f in files:
        try:
            sites = run_driver("scan", f, [], quiet=True)
        except SystemExit as e:
            print(f"{rel(f)}: {e}")
            continue
        counts = {"unused": 0, "exact": 0, "rfl-rw": 0}
        for s in sites:
            k = removable(s)
            if k:
                counts[k] += 1
        total["haves"] += len(sites)
        for k in counts:
            total[k] += counts[k]
        if any(counts.values()) or args.all:
            rows.append((rel(f), len(sites), counts))
            print(f"{rel(f)}: {len(sites)} haves, unused {counts['unused']}, have-then-exact {counts['exact']}, "
                  f"rfl-rw {counts['rfl-rw']}", flush=True)
    print(f"\n{len(files)} files, {total['haves']} haves: unused {total['unused']}, "
          f"have-then-exact {total['exact']}, rfl-rw {total['rfl-rw']}")
    return 0


def module_of(file: Path) -> str:
    return rel(file).removesuffix(".lean").replace("/", ".")


def manifest_path(file: Path) -> Path:
    return MANIFESTS / (module_of(file) + ".json")


def cmd_manifest(args) -> int:
    """Write (or refresh) the triage manifest of each file from a `scan`.

    Judging fields (`verdict`, `proposedLemmaName`, `rationale`, `confidence`, `status`)
    of entries whose declaration and have name still exist are kept."""
    MANIFESTS.mkdir(parents=True, exist_ok=True)
    for f in lean_files(args.files):
        sites = run_driver("scan", f, [], quiet=True)
        path = manifest_path(f)
        old = {}
        if path.exists():
            try:
                for e in json.loads(path.read_text()).get("haves", []):
                    old[(e["declaration"], e["haveName"], e.get("typeText"))] = e
            except json.JSONDecodeError:
                pass
        entries = []
        for i, s in enumerate(sites, 1):
            e = {"id": i, **s}
            prev = old.get((s["declaration"], s["haveName"], s.get("typeText")))
            for k in ("verdict", "proposedLemmaName", "mathlibExisting", "rationale", "confidence", "status", "needsNaming"):
                e[k] = prev.get(k) if prev else None
            if e["status"] is None:
                e["status"] = "scanned"
            entries.append(e)
        judged = all(e["verdict"] for e in entries) and entries
        manifest = {
            "file": rel(f), "scannedAt": date.today().isoformat(),
            "pipelineStage": "judged" if judged else "scanned",
            "metaprogramReady": True, "haves": entries,
        }
        path.write_text(json.dumps(manifest, indent=1, ensure_ascii=False) + "\n")
        print(f"{rel(path)}: {len(entries)} haves"
              + (f", {sum(1 for e in entries if e['status'] == 'queued')} queued" if judged else ""))
    return 0


# ── clean / extract ─────────────────────────────────────────────────────────

def out_path(file: Path) -> Path:
    SCRATCH.mkdir(parents=True, exist_ok=True)
    return SCRATCH / (module_of(file) + ".lean")


def cmd_clean(args) -> int:
    status = 0
    for f in lean_files(args.files):
        print(f"== {rel(f)}")
        extra = []
        for d in args.decl or []:
            extra += ["--decl", d]
        if args.no_unused:
            extra.append("--no-unused")
        if args.no_exact:
            extra.append("--no-exact")
        if args.no_rfl_rw:
            extra.append("--no-rfl-rw")
        out = out_path(f)
        extra += ["--write"] if args.write else ["--out", str(out)]
        report = run_driver("clean", f, extra)
        print_report(report)
        if not report["verified"]:
            status = 1
        if report["changed"] and not args.write and report["verified"]:
            show_diff(f, out)
        if not report["changes"]:
            print("  nothing to remove")
    return status


def cmd_extract(args) -> int:
    f = Path(args.file)
    extra = []
    for t in args.targets:
        extra += ["--target", t]
    if args.private:
        extra.append("--private")
    if args.doc:
        extra += ["--doc", args.doc]
    if args.keyword:
        extra += ["--keyword", args.keyword]
    out = out_path(f)
    extra += ["--write"] if args.write else ["--out", str(out)]
    report = run_driver("extract", f, extra)
    print_report(report)
    if report["changed"] and report["verified"] and not args.write:
        show_diff(f, out)
    return 0 if report["verified"] and not report["skipped"] else 1


def cmd_queue(args) -> int:
    """Convert every manifest entry with `status: "queued"` (the primer's output)."""
    status = 0
    for path in sorted(MANIFESTS.glob("*.json")):
        m = json.loads(path.read_text())
        if args.file and rel(Path(args.file)) != m["file"]:
            continue
        queued = [e for e in m["haves"] if e.get("status") == "queued" and e.get("verdict") == "extract"
                  and e.get("proposedLemmaName")]
        if not queued:
            continue
        targets = [f"{e['declaration']}:{e['haveName']}@{e['line']}:{e['proposedLemmaName']}" for e in queued]
        f = BASE / m["file"]
        print(f"== {m['file']}: {len(targets)} queued")
        extra = []
        for t in targets:
            extra += ["--target", t]
        out = out_path(f)
        extra += ["--write"] if args.write else ["--out", str(out)]
        report = run_driver("extract", f, extra)
        print_report(report)
        if not report["verified"]:
            status = 1
            continue
        if not args.write:
            show_diff(f, out)
            continue
        done = {(c["declaration"], c["have"], c["line"]) for c in report["changes"]}
        failed = {(c["declaration"], c["have"], c["line"]): c["detail"] for c in report["skipped"]}
        for e in m["haves"]:
            key = (e["declaration"], e["haveName"], e["line"])
            if key in done:
                e["status"] = "converted"
            elif key in failed:
                e["status"] = "failed"
                e["failure"] = failed[key]
        path.write_text(json.dumps(m, indent=1, ensure_ascii=False) + "\n")
        if QUEUE.exists():
            text = QUEUE.read_text()
            for (decl, have, line) in done:
                text = re.sub(rf"- \[ \] (`{re.escape(have)}` \(line {line}, in `{re.escape(decl.split('.')[-1])}`\))",
                              r"- [x] \1", text)
            QUEUE.write_text(text)
    return status


# ── tests ───────────────────────────────────────────────────────────────────

#: expected `clean` changes on the fixture: (declaration, have, kind)
EXPECT_CLEAN = {
    ("exact_nested", "h2", "exact"),
    ("unused_and_anonymous", "junk", "unused"),
    ("unused_and_anonymous", "this", "exact"),
    ("rfl_rw_closes", "h", "rfl-rw"),
    ("rfl_rw_continues", "h", "rfl-rw"),
    ("exact_show_needed", "h", "exact"),
    ("bullet", "h1", "exact"),
    ("semicolon", "h", "exact"),
    ("multi_goal", "h1", "exact"),
    ("binders_exact", "h", "exact"),
    ("braced_assumption", "h", "exact"),
    ("rfl_rw_paren", "h", "rfl-rw"),
    ("multi_goal", "h2", "exact"),
    ("unused_with_comment", "junk", "unused"),
    ("binders_dead", "u", "unused"),
    ("binders_dead", "h_expl", "unused"),
    ("intro_vars", "h", "exact"),
    ("inaccessible", "h1", "exact"),
    ("let_dep", "h", "unused"),
    ("implicit_binders", "h", "exact"),
    ("open_in", "h", "exact"),
}

#: expected `extract` outcomes: target → (ok, substring that must appear in the result)
EXPECT_EXTRACT = {
    "used_simp:key:key_of_hab": (True, "theorem key_of_hab (a b : Nat) (hab : a = b) : a = b := by"),
    "exact_nested:h2:le_succ_of_le": (True, "have h3 : b ≤ b + 1 := Nat.le_succ b"),
    "exact_nested:h3:self_le_succ": (True, "theorem self_le_succ (b : Nat) : b ≤ b + 1 := Nat.le_succ b"),
    "binders_used:h_expl:le_succ_of_le_k": (True, "le_succ_of_le_k n k hk"),
    "intro_vars:h:le_succ_of_le_intro": (True, "theorem le_succ_of_le_intro (n m : Nat) (hmn : m ≤ n) : m ≤ n + 1 :="),
    "obtain_vars:h2:p_of_hn": (True, "theorem p_of_hn (P : Nat → Prop) (n : Nat) (hn : P n) : P n := hn"),
    "inaccessible:h1:p_one": (True, "theorem p_one (p : Nat → Prop) (h : ∀ n, p n → p (n+1)) (a : p 0) : p 1 := h 0 ‹p 0›"),
    "inaccessible:h1:p_one@rename": (True, "  rename_i a\n  have h1 : p 1 := p_one p h a"),
    "let_dep:h:let_h": (False, "let-bound"),
    "implicit_binders:h:one_le": (True, "theorem one_le {n : Nat} (hn : 0 < n) : 1 ≤ n := hn"),
    "silent_use:h:succ_le_of_lt": (True, "theorem succ_le_of_lt (a b : Nat) (hab : a < b) : a + 1 ≤ b := by"),
    "destructuring:⟨…⟩:never": (False, "no such have"),
    "open_in:h:le_succ_open": (True, "open Nat in\n/--"),
    "multiline_type:step:step_lemma": (True, "theorem step_lemma (a b : Nat) (h : a ≤ b) : a ≤ b + 1 := by"),
}


def cmd_test(args) -> int:
    failures = 0

    def check(cond: bool, msg: str) -> None:
        nonlocal failures
        print(("  ok   " if cond else "  FAIL ") + msg)
        if not cond:
            failures += 1

    print("scan")
    sites = run_driver("scan", FIXTURES, [], quiet=True)
    by = {(s["declaration"].split(".")[-1], s["haveName"]): s for s in sites}
    check(len(sites) == 30, f"{len(sites)} haves found (expected 30)")
    check(by[("used_simp", "key")]["useCount"] == 1, "used_simp.key used once")
    check(by[("silent_use", "h")]["localDeps"] == ["a", "b", "hab"], "silent_use.h depends on hab through omega")
    check(by[("unused_and_anonymous", "junk")]["unused"], "junk is unused")
    check(by[("unused_and_anonymous", "this")]["exactAfter"], "anonymous have-then-exact")
    check(by[("rfl_rw_closes", "h")]["rflEq"], "rfl equation detected")
    check(by[("inaccessible", "h1")]["inaccessibleDeps"], "inaccessible dependency reported")
    check(by[("inaccessible", "h1")]["localDeps"] == ["p", "h", "a"], "inaccessible dependency given a fresh name")
    check(by[("let_dep", "h")]["letDeps"] == ["m"], "let dependency reported")
    check(by[("destructuring", "⟨…⟩")]["destructuring"], "destructuring have reported")
    check(by[("binders_used", "h_expl")]["binders"] == "(k : Nat) (hk : k ≤ n)", "binders recorded")
    check(by[("exact_with_show", "h")]["exactAfter"] is False, "exact h.symm is not have-then-exact")
    check(by[("hint_only", "h2")]["hintOnly"] and not by[("hint_only", "h2")]["unused"], "hint-only use reported, not unused")
    check(by[("silent_use", "h")]["useCount"] == 1, "silent_use.h used")

    print("clean")
    out = out_path(FIXTURES)
    report = run_driver("clean", FIXTURES, ["--out", str(out)], quiet=True)
    check(report["verified"], "rewritten fixture elaborates")
    got = {(c["declaration"].split(".")[-1], c["have"], c["kind"]) for c in report["changes"]}
    for e in sorted(EXPECT_CLEAN):
        check(e in got, f"clean {e[0]}.{e[1]} ({e[2]})")
    for g in sorted(got - EXPECT_CLEAN):
        check(False, f"unexpected clean change {g}")
    text = out.read_text() if out.exists() else ""
    check("exact (rfl : n = n)" in text, "type kept when it is only definitionally the goal")
    check("  -- this comment stays\n  rfl" in text, "comment before the next tactic kept")
    check("  change (n + 1 = n + 1)" not in text and "change n + 1 = n + 1\n  rfl" in text, "change without the parentheses, then rfl")
    check("change n + 0 = 0\n  omega" in text, "change followed by the rest of the proof")
    check("  · exact Nat.add_zero n\n" in text, "bullet body inlined")
    check("  constructor\n  · exact Nat.add_zero n\n  · exact Nat.zero_add n\n" in text, "blocks closing successive goals get bullets")
    check("theorem semicolon (n : Nat) : n ≤ n + 1 := by\n  exact Nat.le_succ n" in text, "semicolon form inlined")
    check("  intro k hk\n  show k ≤ n + 1\n  omega" in text, "binders become intro, then show, then the proof")
    check("theorem braced_assumption (n : Nat) : n ≤ n + 1 := by\n  apply Nat.le_succ" in text, "braced block inlined, assumption consumed")
    check("theorem rfl_rw_paren (n : Nat) : (fun x => x + 1) n = n + 1 := by\n  change n + 1 = n + 1\n  rfl" in text, "parenthesized rfl equation handled")

    print("extract")
    for target, (ok, needle) in EXPECT_EXTRACT.items():
        out = out_path(FIXTURES)
        if out.exists():
            out.unlink()
        report = run_driver("extract", FIXTURES, ["--target", target.split("@rename")[0], "--out", str(out)], quiet=True)
        if ok:
            text = out.read_text() if out.exists() else ""
            check(report["verified"] and report["changes"] and needle in text,
                  f"extract {target}" + ("" if needle in text else f" -- missing {needle!r}"))
        else:
            detail = " ".join(c["detail"] for c in report["skipped"])
            check(not report["changes"] and needle in detail, f"extract {target} refused ({needle})")
    print(f"\n{'ALL PASSED' if not failures else f'{failures} FAILURE(S)'}")
    return 1 if failures else 0


# ── main ────────────────────────────────────────────────────────────────────

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("scan"); p.add_argument("file"); p.add_argument("--json", action="store_true")
    p = sub.add_parser("census"); p.add_argument("paths", nargs="*"); p.add_argument("--all", action="store_true")
    p = sub.add_parser("manifest"); p.add_argument("files", nargs="+")
    p = sub.add_parser("clean"); p.add_argument("files", nargs="+"); p.add_argument("--write", action="store_true")
    p.add_argument("--decl", action="append"); p.add_argument("--no-unused", action="store_true")
    p.add_argument("--no-exact", action="store_true"); p.add_argument("--no-rfl-rw", action="store_true")
    p = sub.add_parser("extract"); p.add_argument("file"); p.add_argument("targets", nargs="+")
    p.add_argument("--write", action="store_true"); p.add_argument("--private", action="store_true")
    p.add_argument("--doc"); p.add_argument("--keyword", choices=["lemma", "theorem"])
    p = sub.add_parser("queue"); p.add_argument("--write", action="store_true"); p.add_argument("--file")
    sub.add_parser("test")
    args = ap.parse_args()
    return {"scan": cmd_scan, "census": cmd_census, "manifest": cmd_manifest, "clean": cmd_clean,
            "extract": cmd_extract, "queue": cmd_queue, "test": cmd_test}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
