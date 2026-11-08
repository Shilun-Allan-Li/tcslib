r"""Refresh compiler-derived blueprint dependencies without replacing prose or citations.

Mutually defined declarations are simultaneous nodes. Their internal edges remain
in dep_graph.json and are recorded in a comment, rather than creating a cycle in
the renderer's acyclic \uses graph.
"""

import argparse
import json
from pathlib import Path
import re
import sys

BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))
from scripts import build_dataset as bd
from scripts import blueprint_enumerate as be

ENTRY_RE = re.compile(r"\\begin\{(?P<env>theorem|lemma|definition|proposition|corollary|sublemma)\}"
                      r"[\s\S]*?\\end\{(?P=env)\}")
LEAN_RE = re.compile(r"\\lean\{([^}]*)\}")
USES_RE = re.compile(r"^\\uses\{[^}]*\}\n?", re.M)
SIMULTANEOUS_RE = re.compile(r"^% simultaneous-definitions:[^\n]*\n?", re.M)


def refresh_entry(text, dependencies, simultaneous):
    names = {n.strip() for m in LEAN_RE.finditer(text) for n in m[1].split(",") if n.strip()}
    if not names or not names <= dependencies.keys():
        return text
    uses = set().union(*(dependencies[n] - simultaneous.get(n, set()) for n in names)) - names
    peers = set().union(*(simultaneous.get(n, set()) for n in names)) - names
    text = SIMULTANEOUS_RE.sub("", USES_RE.sub("", text))
    lines = []
    if uses:
        lines.append("\\uses{" + ", ".join(sorted(uses)) + "}")
    if peers:
        lines.append("% simultaneous-definitions: " + ", ".join(sorted(peers)))
    if lines:
        anchor = re.search(r"\\leanok[^\n]*\n", text)
        at = anchor.end() if anchor else text.index("\n", LEAN_RE.search(text).end()) + 1
        text = text[:at] + "\n".join(lines) + "\n" + text[at:]
    return text


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--apply", action="store_true")
    parser.add_argument("--only", nargs="+")
    parser.add_argument("--modules", nargs="+")
    args = parser.parse_args()
    graph = json.loads((BASE / "dep_graph.json").read_text())["modules"]
    index = bd.build_index(graph)
    kept = be.build_kept_global(graph)
    dependencies = {}
    simultaneous = {}
    for module, data in graph.items():
        path = bd.module_to_lean_path(module)
        lines = path.read_text().splitlines()
        _, by_kidx, _ = bd.parse_module_items(lines)
        groups = {}
        for raw, dd in data["declarations"].items():
            name = bd.normalize_name(raw)
            if name not in index or name not in kept or index[name]["module"] != module:
                continue
            dependencies[name] = {bd.normalize_name(d["name"]) for d in dd.get("deps", [])
                                  if bd.dp.is_internal(d["module"]) and bd.normalize_name(d["name"]) in kept}
            item = by_kidx.get(index[name]["kidx"])
            if item and bd.MUTUAL_START_RE.match(lines[item["start"]]):
                groups.setdefault(item["start"], set()).add(name)
        for group in groups.values():
            for name in group:
                simultaneous[name] = group - {name}
    changed = entries = 0
    for path in sorted((BASE / "blueprint/src/chapter").rglob("*.tex")):
        original = path.read_text()
        def update(match):
            nonlocal entries
            text = match[0]
            names = {n.strip() for m in LEAN_RE.finditer(text) for n in m[1].split(",")}
            if args.only and not names & set(args.only):
                return text
            if args.modules and not any(n in index and bd.module_matches(index[n]["module"], args.modules)
                                        for n in names):
                return text
            revised = refresh_entry(text, dependencies, simultaneous)
            entries += revised != text
            return revised
        revised = ENTRY_RE.sub(update, original)
        if revised != original:
            changed += 1
            if args.apply:
                path.write_text(revised)
    print(f"{'Refreshed' if args.apply else 'Would refresh'} dependencies of {entries} entries in {changed} files; "
          f"{len(simultaneous)} mutually defined declarations recorded separately")


if __name__ == "__main__":
    main()
