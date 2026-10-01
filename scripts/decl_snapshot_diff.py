#!/usr/bin/env python3
"""
Invariance gate for the policy cleanup: compare two decl_snapshot labels.

    python3 scripts/decl_snapshot_diff.py before after [--renames cleanup/renames.json]

Declarations are keyed by unmangled full name across ALL modules in a label, so
moving a declaration to another file is transparent.  The gate FAILS on:

  MISSING        a declaration in `before` is absent from `after`
                 (unless listed in renames.json as {"old": "new"})
  TYPE           statement / type changed (structural, alpha-invariant hash)
  VALUE          body of a def / opaque / inductive / ctor changed
  KIND / LEVELS / VISIBILITY   kind, universe params, or `private` changed
  SORRY          any declaration in `after` depends on sorryAx
  AXIOM          a declaration in `after` uses an axiom outside
                 {propext, Quot.sound, Classical.choice} that it did not use before
  SNAPSHOT-ERROR a module in `after` did not elaborate cleanly

It WARNS (does not fail) on:
  NEW            a declaration present only in `after` (new helper lemmas are fine)
  MOVED          module changed
  STDAXIOM       a proof now uses one of the three standard axioms it did not before

Exit code 0 = invariant holds, 1 = violated.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SNAP_ROOT = ROOT / "cleanup" / "snapshots"
STD_AXIOMS = {"propext", "Quot.sound", "Classical.choice"}
# `private` names are mangled with their defining module (`_private.<Mod>.0.foo`), so a
# private declaration that moves to another file changes its *name* inside every term that
# mentions it (including its own `_proof_n` aux lemmas) without any content change.  When
# hashes differ, fall back to comparing the fully-explicit `pp.all` text with the module
# stripped from private prefixes; equal text ⇒ same term.
_PRIV = re.compile(r"_private\.[A-Za-z0-9_.«»]+?\.0\.")


def _norm(pp: str | None) -> str | None:
    return None if pp is None else _PRIV.sub("_private.", pp)


def same_term(a_hash, b_hash, a_pp, b_pp, a_ni=None, b_ni=None) -> bool:
    """Equal hash; else equal explicit text modulo private mangling; else equal explicit
    text with instance arguments elided (import changes can re-route instance resolution
    to a definitionally equal instance without touching the statement)."""
    if a_hash == b_hash:
        return True
    if a_pp is not None and _norm(a_pp) == _norm(b_pp):
        return True
    return a_ni is not None and b_ni is not None and _norm(a_ni) == _norm(b_ni)


def load(label: str) -> tuple[dict[str, dict], list[str]]:
    decls: dict[str, dict] = {}
    errors: list[str] = []
    d = SNAP_ROOT / label
    if not d.is_dir():
        sys.exit(f"no snapshot label {label!r} under {SNAP_ROOT}")
    for f in sorted(d.glob("*.json")):
        j = json.loads(f.read_text())
        if j.get("errors"):
            errors.append(f"{j['module']}: {j['errors'][0][:200]}")
        for x in j["declarations"]:
            if x["name"] in decls:
                errors.append(f"duplicate declaration name across modules: {x['name']}")
            decls[x["name"]] = x
    return decls, errors


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("before")
    ap.add_argument("after")
    ap.add_argument("--renames", default=str(ROOT / "cleanup" / "renames.json"))
    ap.add_argument("--quiet", action="store_true")
    ap.add_argument("--accept-kind", default="",
                    help="comma-separated declaration names whose KIND may change (e.g. an axiom "
                         "that has been proved: axiom → thm); user-approved, listed in the report")
    ap.add_argument("--accept-visibility", default="",
                    help="comma-separated declaration names whose `private` flag may change")
    ap.add_argument("--after-prefix", default="",
                    help="only consider `after` declarations whose module starts with this prefix "
                         "(e.g. TCSlib.LearningTheory) — for a shared after-label holding several areas")
    ap.add_argument("--before-modules", default="",
                    help="comma-separated module names: restrict the `before` side to declarations "
                         "that lived in these modules (for a partial after-label taken on one topic)")
    args = ap.parse_args()

    renames: dict[str, str] = {}
    if Path(args.renames).exists():
        renames = json.loads(Path(args.renames).read_text())

    accept_kind = {n.strip() for n in args.accept_kind.split(",") if n.strip()}
    accept_vis = {n.strip() for n in args.accept_visibility.split(",") if n.strip()}
    before, _ = load(args.before)
    after, after_errors = load(args.after)
    if args.after_prefix:
        after = {n: d for n, d in after.items() if d["module"].startswith(args.after_prefix)}
        after_errors = [e for e in after_errors if e.split(":")[0].startswith(args.after_prefix)]
    if args.before_modules:
        mods = {m.strip() for m in args.before_modules.split(",") if m.strip()}
        unknown = mods - {d["module"] for d in before.values()}
        if unknown:
            sys.exit(f"--before-modules names not in `{args.before}`: {sorted(unknown)}")
        full_before_modules = {d["module"] for d in before.values()}
        before = {n: d for n, d in before.items() if d["module"] in mods}
        # on the after side keep only the scoped declarations and anything in a module that
        # did not exist at baseline (new split pieces); untouched old modules are ignored
        after = {n: d for n, d in after.items()
                 if n in before or d["module"] in mods
                 or d["module"] not in full_before_modules}
        after_errors = [e for e in after_errors
                        if e.split(":")[0] in mods or e.split(":")[0] not in full_before_modules]

    fails: list[str] = []
    warns: list[str] = []
    for e in after_errors:
        fails.append(f"SNAPSHOT-ERROR  {e}")

    seen_after: set[str] = set()
    for name, b in before.items():
        new_name = renames.get(name, name)
        a = after.get(new_name)
        if a is None:
            fails.append(f"MISSING         {name}" + (f" (renamed → {new_name})" if new_name != name else ""))
            continue
        seen_after.add(new_name)
        tag = name if new_name == name else f"{name} → {new_name}"
        if a["kind"] != b["kind"]:
            if name in accept_kind and b["kind"] == "axiom" and a["kind"] == "thm":
                warns.append(f"KIND-ACCEPTED   {tag}: axiom → thm (user-approved)")
            else:
                fails.append(f"KIND            {tag}: {b['kind']} → {a['kind']}")
        if a["levelParams"] != b["levelParams"]:
            fails.append(f"LEVELS          {tag}: {b['levelParams']} → {a['levelParams']}")
        if a["private"] != b["private"]:
            if name in accept_vis:
                warns.append(f"VIS-ACCEPTED    {tag}: private {b['private']} → {a['private']} (user-approved)")
            else:
                fails.append(f"VISIBILITY      {tag}: private {b['private']} → {a['private']}")
        if not same_term(a["typeHash"], b["typeHash"], a["typePP"], b["typePP"],
                         a.get("typeNI"), b.get("typeNI")):
            fails.append(f"TYPE            {tag}\n    before: {b['typePP']}\n    after:  {a['typePP']}")
        if b["kind"] != "thm" and not same_term(a.get("valueHash"), b.get("valueHash"),
                                                a.get("valuePP"), b.get("valuePP"),
                                                a.get("valueNI"), b.get("valueNI")):
            fails.append(f"VALUE           {tag} ({b['kind']} body changed)")
        if a["module"] != b["module"]:
            warns.append(f"MOVED           {tag}: {b['module']} → {a['module']}")
        new_ax = set(a["axioms"]) - set(b["axioms"])
        if "sorryAx" in a["axioms"]:
            fails.append(f"SORRY           {tag}")
            new_ax.discard("sorryAx")
        for ax in sorted(new_ax):
            if ax in STD_AXIOMS:
                warns.append(f"STDAXIOM        {tag}: now uses {ax}")
            else:
                fails.append(f"AXIOM           {tag}: now uses {ax}")

    for name, a in after.items():
        if name in seen_after:
            continue
        if "sorryAx" in a["axioms"]:
            fails.append(f"SORRY           {name} (new declaration)")
        else:
            warns.append(f"NEW             {name} [{a['kind']}] in {a['module']}")
        extra = set(a["axioms"]) - STD_AXIOMS - {"sorryAx"}
        for ax in sorted(extra):
            fails.append(f"AXIOM           {name} (new declaration) uses {ax}")

    if not args.quiet:
        for w in warns:
            print("warn  " + w)
        for f in fails:
            print("FAIL  " + f)
    print(f"\n{len(before)} declarations before, {len(after)} after; "
          f"{len(fails)} violations, {len(warns)} warnings")
    print("INVARIANT HOLDS" if not fails else "INVARIANT VIOLATED")
    return 1 if fails else 0


if __name__ == "__main__":
    sys.exit(main())
