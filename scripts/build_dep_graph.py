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
import sys
from pathlib import Path


BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))
from scripts import dataset_projects as dp

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

    def record(tuple_: object) -> None:
        if (
            isinstance(tuple_, list)
            and len(tuple_) >= 9
            and isinstance(tuple_[4], str)
        ):
            name = tuple_[4]
            # Lean's .ilean positions are zero-based; the graph exposes source
            # locations as one-based line numbers.
            sl, el = tuple_[5] + 1, tuple_[7] + 1
            if name not in ranges:
                ranges[name] = [sl, el]
            else:
                ranges[name][0] = min(ranges[name][0], sl)
                ranges[name][1] = max(ranges[name][1], el)

    for v in refs.values():
        # `usages` names the *enclosing* declaration, so a declaration is only seen
        # here if something inside its body produced an extended reference. An
        # `inductive` attributes its inner references to its constructors, never to
        # itself, so `PauliBasis` was absent from the graph entirely — invisible to the
        # dataset, to routing, and to the validator's orphan check, and it blocked three
        # upstream mappings. Its own `definition` tuple carries exactly the same shape
        # (name at index 4, range at 5/7), so seed from that too: any body-less
        # declaration is authoritative about itself.
        record(v.get("definition"))
        for usage in v.get("usages", []):
            record(usage)
    return ranges


def find_enclosing_decl(line: int, sorted_ranges: list[tuple]) -> str | None:
    """Find the innermost declaration containing `line` (latest start wins)."""
    matches = [(sl, el, name) for sl, el, name in sorted_ranges if sl <= line <= el]
    if not matches:
        return None
    return max(matches, key=lambda x: x[0])[2]


def parse_ilean(path: Path, source: Path | None = None) -> dict:
    with open(path) as f:
        data = json.load(f)

    module = data.get("module", "")
    direct_imports = [entry[0] for entry in data.get("directImports", [])]
    refs = data.get("references", {})

    # Lean 4.32 moved declaration ranges out of each usage tuple into `decls`.
    # The first four positions span the declaration (including its docstring);
    # the last four span its identifier. Lean 4.25 uses extended usage tuples.
    if "decls" in data:
        decl_ranges = {name: [pos[0] + 1, pos[2] + 1]
                       for name, pos in data["decls"].items()}
    else:
        decl_ranges = build_decl_ranges(refs)
    # Older reference indexes give unused constants only a four-position identifier
    # location. Recover their full source span while retaining compiler-given names.
    if source is not None and "decls" not in data:
        from scripts.build_dataset import parse_module_items, normalize_name, declared_short_name
        lines = source.read_text().splitlines()
        _, by_keyword, _ = parse_module_items(lines)
        for key, value in refs.items():
            constant = json.loads(key).get("c", {})
            pos = value.get("definition")
            name = constant.get("n")
            if constant.get("m") != module or not name or name in decl_ranges or not pos:
                continue
            for keyword, item in by_keyword.items():
                if keyword <= pos[0] < item["end"] and declared_short_name(
                        "\n".join(lines[keyword:keyword + 5])) == normalize_name(name).split(".")[-1]:
                    decl_ranges[name] = [keyword + 1, item["end"]]
                    break
    sorted_ranges = sorted((r[0], r[1], n) for n, r in decl_ranges.items())

    # deps[decl_name] -> set of (src_module, const_name)
    deps: dict[str, set] = {name: set() for name in decl_ranges}

    for ref_key_str, ref_val in refs.items():
        ref_key = json.loads(ref_key_str)
        if "c" not in ref_key:
            continue
        src_module = ref_key["c"]["m"]
        const_name = ref_key["c"]["n"]
        for usage in ref_val.get("usages", []):
            if len(usage) >= 5 and isinstance(usage[4], str):
                # Intra-module: enclosing decl name is explicit
                enclosing = usage[4]
            else:
                # Inter-module: map usage line to enclosing decl via ranges
                enclosing = find_enclosing_decl(usage[0] + 1, sorted_ranges)

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


def prune_impossible_forward_refs(parsed: dict, source: Path) -> list[dict]:
    """Exclude reference-index aliases to later, unavailable local declarations.

    Lean 4.25's reference index can attach a local binder's occurrences to a
    later constant name. Such an edge cannot be an elaborated dependency.
    Actual mutual declarations are exempt. Keep every excluded edge in the
    graph's audit metadata rather than silently turning it into a dependency.
    """
    from scripts.build_dataset import parse_module_items, MUTUAL_START_RE
    lines = source.read_text().splitlines()
    items, _, _ = parse_module_items(lines)
    mutual = [(it["start"] + 1, it["end"]) for it in items
              if it["type"] == "decl" and MUTUAL_START_RE.match(lines[it["start"]])]
    decls = parsed["declarations"]
    discarded = []
    for name, declaration in decls.items():
        retained = []
        for dep in declaration["deps"]:
            target = decls.get(dep["name"]) if dep["module"] == parsed["module"] else None
            forward = target is not None and target["startLine"] > declaration["endLine"]
            simultaneous = forward and any(
                lo <= declaration["startLine"] <= hi and lo <= target["startLine"] <= hi
                for lo, hi in mutual)
            if forward and not simultaneous:
                discarded.append({"from": name, "to": dep["name"],
                                  "reason": "later declaration outside a mutual block"})
            else:
                retained.append(dep)
        declaration["deps"] = retained
    return discarded


def build_graph(root: Path, source_root: Path | None = None) -> dict:
    source_root = source_root or Path.cwd()
    graph = {}
    ilean_files = find_ilean_files(root)
    print(f"Found {len(ilean_files)} .ilean files")

    for path in ilean_files:
        guessed_module = ilean_module_name(path, root)
        source = source_root / (guessed_module.replace(".", "/") + ".lean")
        parsed = parse_ilean(path, source if source.is_file() else None)
        module = parsed["module"]
        if not module:
            module = ilean_module_name(path, root)
        # Renamed/deleted modules can leave cached artifacts behind. Only live
        # source modules belong in the declaration graph.
        source = source_root / (module.replace(".", "/") + ".lean")
        if not source.is_file():
            continue
        discarded = prune_impossible_forward_refs(parsed, source)
        graph[module] = {
            "source_sha256": dp.sha256(source),
            "artifact_sha256": dp.sha256(path),
            "discarded_forward_references": discarded,
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

    graph = {}
    project_info = {}
    for name, project_root in dp.projects().items():
        artifacts = root if name == "TCSlib" else project_root / ".lake/build/lib/lean" / name
        if not artifacts.is_dir():
            raise FileNotFoundError(f"Missing compiled artifacts: {artifacts}")
        graph.update(build_graph(artifacts, project_root))
        project_info[name] = dp.provenance(name, project_root)

    out_path = Path(args.out)
    with open(out_path, "w") as f:
        json.dump({"projects": project_info, "modules": graph}, f, indent=2)

    total_decls = sum(len(m["declarations"]) for m in graph.values())
    print(f"\nWrote {out_path}: {len(graph)} modules, {total_decls} declarations")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
