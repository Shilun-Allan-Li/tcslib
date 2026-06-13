"""
Build a declaration-level dependency graph from Lean .ilean build artifacts.

Reads all TCSlib .ilean files from .lake/build/lib/lean/TCSlib/ and produces
dep_graph.json with:
  - modules: module -> { directImports, declarations }
  - declarations: decl_name -> { module, startLine, endLine, deps[] }

Usage:
    python3 scripts/build_dep_graph.py [--out dep_graph.json]

Requires the project to have been built at least once (ilean files must exist).
"""

import json
import argparse
from pathlib import Path


ILEAN_ROOT = Path(".lake/build/lib/lean/TCSlib")
DEFAULT_OUT = Path("dep_graph.json")


def find_ilean_files(root: Path) -> list[Path]:
    return sorted(root.rglob("*.ilean"))


def ilean_module_name(path: Path, root: Path) -> str:
    rel = path.relative_to(root.parent)  # relative to lib/lean/
    return str(rel.with_suffix("")).replace("/", ".")


def build_decl_ranges(refs: dict) -> dict[str, list[int]]:
    """
    Extract full declaration line ranges from the extended usage tuples.
    Extended tuple format: [useSL, useSC, useEL, useEC, declName, declSL, declSC, declEL, declEC, ...]
    Returns: { decl_name: [startLine, endLine] }
    """
    ranges: dict[str, list[int]] = {}
    for v in refs.values():
        for usage in v.get("usages", []):
            if len(usage) >= 9 and isinstance(usage[4], str):
                name = usage[4]
                sl, el = usage[5], usage[7]
                if name not in ranges:
                    ranges[name] = [sl, el]
                else:
                    ranges[name][0] = min(ranges[name][0], sl)
                    ranges[name][1] = max(ranges[name][1], el)
    return ranges


def find_enclosing_decl(line: int, sorted_ranges: list[tuple]) -> str | None:
    """Find the innermost declaration containing `line` (latest start wins)."""
    matches = [(sl, el, name) for sl, el, name in sorted_ranges if sl <= line <= el]
    if not matches:
        return None
    return max(matches, key=lambda x: x[0])[2]


def parse_ilean(path: Path) -> dict:
    with open(path) as f:
        data = json.load(f)

    module = data.get("module", "")
    direct_imports = [entry[0] for entry in data.get("directImports", [])]
    refs = data.get("references", {})

    decl_ranges = build_decl_ranges(refs)
    sorted_ranges = sorted((r[0], r[1], n) for n, r in decl_ranges.items())

    # deps[decl_name] -> set of (src_module, const_name)
    deps: dict[str, set] = {name: set() for name in decl_ranges}

    for ref_key_str, ref_val in refs.items():
        ref_key = json.loads(ref_key_str)
        if "c" not in ref_key:
            continue
        src_module = ref_key["c"]["m"]
        const_name = ref_key["c"]["n"]
        defn = ref_val.get("definition")

        for usage in ref_val.get("usages", []):
            if defn is not None and len(usage) >= 9 and isinstance(usage[4], str):
                # Intra-module: enclosing decl name is explicit
                enclosing = usage[4]
            else:
                # Inter-module: map usage line to enclosing decl via ranges
                enclosing = find_enclosing_decl(usage[0], sorted_ranges)

            if enclosing and enclosing in deps:
                if not (src_module == module and const_name == enclosing):
                    deps[enclosing].add((src_module, const_name))

    declarations = {}
    for name, (sl, el) in decl_ranges.items():
        declarations[name] = {
            "startLine": sl,
            "endLine": el,
            "deps": [{"module": m, "name": n} for m, n in sorted(deps.get(name, set()))],
        }

    return {
        "module": module,
        "directImports": direct_imports,
        "declarations": declarations,
    }


def build_graph(root: Path) -> dict:
    graph = {}
    ilean_files = find_ilean_files(root)
    print(f"Found {len(ilean_files)} .ilean files")

    for path in ilean_files:
        parsed = parse_ilean(path)
        module = parsed["module"]
        if not module:
            module = ilean_module_name(path, root)
        graph[module] = {
            "directImports": parsed["directImports"],
            "declarations": parsed["declarations"],
        }
        print(f"  {module}: {len(parsed['declarations'])} decls")

    return graph


def upstream_modules(module: str, graph: dict) -> set[str]:
    """Transitive closure of direct imports for a given module."""
    visited = set()
    stack = [module]
    while stack:
        m = stack.pop()
        if m in visited:
            continue
        visited.add(m)
        for imp in graph.get(m, {}).get("directImports", []):
            stack.append(imp)
    visited.discard(module)
    return visited


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", default=str(DEFAULT_OUT), help="Output JSON path")
    parser.add_argument("--root", default=str(ILEAN_ROOT), help="Path to .ilean root")
    args = parser.parse_args()

    root = Path(args.root)
    if not root.exists():
        print(f"ERROR: ilean root not found: {root}")
        print("Build the project first (lake build) to generate .ilean files.")
        return 1

    graph = build_graph(root)

    out_path = Path(args.out)
    with open(out_path, "w") as f:
        json.dump({"modules": graph}, f, indent=2)

    total_decls = sum(len(m["declarations"]) for m in graph.values())
    print(f"\nWrote {out_path}: {len(graph)} modules, {total_decls} declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
