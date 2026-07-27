#!/usr/bin/env python3
"""Adversarial candidate scanner for the have->lemma extraction pipeline.

Scans TCSlib/**/*.lean for declarations with haves, scores them by
risky-idiom density (the idioms that have historically broken
ExtractHavesFile.lean), skips everything already recorded in the ledger,
and emits the top candidates as ready-to-paste #extract_haves_iter_decl
driver lines.

Usage:
  python3 scripts/adversarial_scan.py                 # top 5 candidate files
  python3 scripts/adversarial_scan.py --top 8
  python3 scripts/adversarial_scan.py --record FILE DECL RESULT [NOTE...]
  python3 scripts/adversarial_scan.py --cleanup       # rm all *_iter_output* / *.progress
  python3 scripts/adversarial_scan.py --ledger        # print ledger summary

Ledger: scripts/adversarial_ledger.json
  { "tested": { "<relpath>::<decl>": {"date":..., "result":..., "note":...} } }
  result is free-form; convention: "pass N/N", "partial K/N <class>",
  "skip-baseline", "fail <class>".
"""
import json, os, re, subprocess, sys, datetime

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEDGER = os.path.join(ROOT, "scripts", "adversarial_ledger.json")

# (regex on decl body lines, weight, tag)
RISK = [
    (re.compile(r"\bcases .* with\b"), 2, "cases-with"),
    (re.compile(r"\binduction'? .*\bwith\b"), 2, "induction-with"),
    (re.compile(r"^\s*(·\s*)?split\b"), 2, "split"),
    (re.compile(r"^\s*(·\s*)?next\b"), 2, "next-arm"),
    (re.compile(r"\bhave ⟨"), 3, "destr-have"),
    (re.compile(r"^\s*let \w+ : [^=]*$"), 3, "match-lambda-let"),
    (re.compile(r"^\s*let \w+.*:="), 1, "tactic-let"),
    (re.compile(r"^\s*set \w+"), 1, "set"),
    (re.compile(r"\bcalc\b"), 1, "calc"),
    (re.compile(r"^\s*termination_by\b"), 2, "self-recursion"),
    (re.compile(r"^\s*where\b"), 3, "where"),
    (re.compile(r"\bmatch .* with\b"), 1, "match"),
    (re.compile(r"^\s*obtain ⟨"), 1, "obtain"),
]
DECL_RE = re.compile(r"^(private )?(theorem|lemma) ([\w.']+)")
HAVE_RE = re.compile(r"^\s+(·\s*)?have[\s⟨]")


def load_ledger():
    if os.path.exists(LEDGER):
        with open(LEDGER) as f:
            return json.load(f)
    return {"tested": {}}


def save_ledger(led):
    with open(LEDGER, "w") as f:
        json.dump(led, f, indent=1, ensure_ascii=False)


def scan():
    led = load_ledger()
    tested = led["tested"]
    out = []
    for dirpath, _dirs, files in os.walk(os.path.join(ROOT, "TCSlib")):
        if "Tactics" in dirpath.split(os.sep):
            continue
        for fn in files:
            if not fn.endswith(".lean") or "_iter_output" in fn or "_output" in fn:
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            if f"{rel}::*" in tested:  # whole-file campaign already done
                continue
            lines = open(path, encoding="utf-8").read().split("\n")
            file_mutual = sum(1 for l in lines if l.startswith("mutual"))
            file_autoimp = not any(l.strip() == "set_option autoImplicit false" for l in lines)
            cur, body = None, []
            decls = []
            for l in lines + ["end-of-file-sentinel"]:
                m = DECL_RE.match(l)
                if m or l == "end-of-file-sentinel":
                    if cur:
                        decls.append((cur, body))
                    cur = m.group(3) if m else None
                    body = []
                elif cur is not None:
                    if l and not l[0].isspace() and not l.startswith(")"):
                        decls.append((cur, body))
                        cur, body = None, []
                    else:
                        body.append(l)
            for name, blines in decls:
                key = f"{rel}::{name}"
                if key in tested:
                    continue
                haves = sum(1 for b in blines if HAVE_RE.match(b))
                if haves == 0:
                    continue
                score, tags = 0, set()
                for rx, w, tag in RISK:
                    hits = sum(1 for b in blines if rx.search(b))
                    if hits:
                        score += w * min(hits, 3)
                        tags.add(tag)
                if file_mutual:
                    score += 2; tags.add("mutual-file")
                if file_autoimp:
                    score += 1; tags.add("autoImplicit-file")
                # prefer mid-size decls: monsters time out, 1-have decls teach little
                size_bonus = 3 if 3 <= haves <= 15 else (1 if haves > 15 else 0)
                out.append((score + size_bonus, haves, rel, name, sorted(tags)))
    out.sort(reverse=True)
    # one decl per file (the best), files ranked by that decl
    seen_files, picks = set(), []
    for s, h, rel, name, tags in out:
        if rel in seen_files:
            continue
        seen_files.add(rel)
        picks.append((s, h, rel, name, tags))
    return picks


def main():
    args = sys.argv[1:]
    if args[:1] == ["--record"]:
        rel, decl, result = args[1], args[2], args[3]
        note = " ".join(args[4:])
        led = load_ledger()
        led["tested"][f"{rel}::{decl}"] = {
            "date": datetime.date.today().isoformat(), "result": result, "note": note}
        save_ledger(led)
        print(f"recorded {rel}::{decl} = {result}")
        return
    if args[:1] == ["--cleanup"]:
        n = 0
        for dirpath, _d, files in os.walk(os.path.join(ROOT, "TCSlib")):
            for fn in files:
                if "_iter_output" in fn or fn.endswith(".progress"):
                    os.remove(os.path.join(dirpath, fn)); n += 1
                    print("rm", os.path.join(os.path.relpath(dirpath, ROOT), fn))
        print(f"cleaned {n} files")
        return
    if args[:1] == ["--ledger"]:
        led = load_ledger()
        for k, v in sorted(led["tested"].items()):
            print(f"{v['date']}  {v['result']:<28} {k}   {v.get('note','')}")
        print(f"total: {len(led['tested'])}")
        return
    top = int(args[args.index("--top") + 1]) if "--top" in args else 5
    picks = scan()[:top]
    if not picks:
        print("No untested candidates with haves remain."); return
    print("rank score haves  file :: decl  [tags]")
    for i, (s, h, rel, name, tags) in enumerate(picks, 1):
        print(f"{i:>4} {s:>5} {h:>5}  {rel} :: {name}  {tags}")
    print("\n-- driver lines (paste into TCSlib/Tactics/Test.lean after imports) --")
    for _s, _h, rel, name, _t in picks:
        outp = rel.replace(".lean", "_iter_output.lean")
        print(f'#extract_haves_iter_decl "{rel}" "{outp}" "{name}"')
    print("\n-- imports --")
    for _s, _h, rel, _n, _t in picks:
        mod = rel.replace("/", ".").replace(".lean", "")
        print(f"import {mod}")


if __name__ == "__main__":
    main()
