"""
Query the dependency graph built by build_dep_graph.py.

Usage:
    # Transitive upstream declarations for a specific declaration
    python3 scripts/query_deps.py upstream "BooleanAnalysis.chiS_sq_eq_one"

    # Transitive upstream, TCSlib-only
    python3 scripts/query_deps.py upstream "BooleanAnalysis.chiS_sq_eq_one" --tcslib-only

    # List all declarations in a module
    python3 scripts/query_deps.py list TCSlib.BooleanAnalysis.Basic

    # Find which module defines a declaration
    python3 scripts/query_deps.py find "BooleanAnalysis.chiS"
"""

import json
import argparse
from pathlib import Path


DEP_GRAPH = Path("dep_graph.json")


def load_graph(path: Path = DEP_GRAPH) -> dict:
    with open(path) as f:
        return json.load(f)["modules"]


def all_declarations(graph: dict) -> dict[str, dict]:
    """Flat map: fully_qualified_or_short_name -> {module, startLine, endLine, deps}"""
    result = {}
    for module, mdata in graph.items():
        for decl_name, ddata in mdata["declarations"].items():
            result[decl_name] = {"module": module, **ddata}
    return result


def find_decl(name: str, decls: dict) -> list[str]:
    """Find all decl keys matching `name` (exact or suffix match)."""
    exact = [k for k in decls if k == name]
    if exact:
        return exact
    return [k for k in decls if k.endswith("." + name) or k == name]


def upstream(decl_name: str, graph: dict, tcslib_only: bool = False) -> dict[str, dict]:
    """
    Compute transitive upstream declarations for decl_name.
    Returns { decl_name: {module, startLine, endLine, deps} }
    """
    decls = all_declarations(graph)
    matches = find_decl(decl_name, decls)
    if not matches:
        raise KeyError(f"Declaration not found: {decl_name!r}")
    if len(matches) > 1:
        print(f"Ambiguous name {decl_name!r}, matches: {matches}")
        print("Using first match.")
    root = matches[0]

    visited: dict[str, dict] = {}
    stack = [root]
    while stack:
        name = stack.pop()
        if name in visited:
            continue
        info = decls.get(name)
        if info is None:
            continue
        if tcslib_only and not info["module"].startswith("TCSlib"):
            continue
        visited[name] = info
        for dep in info.get("deps", []):
            dep_name = dep["name"]
            if dep_name not in visited:
                stack.append(dep_name)

    visited.pop(root, None)
    return visited


def cmd_upstream(args, graph):
    result = upstream(args.name, graph, tcslib_only=args.tcslib_only)
    decls = all_declarations(graph)
    root_matches = find_decl(args.name, decls)
    root = root_matches[0] if root_matches else args.name

    print(f"Upstream of: {root}")
    print(f"Total upstream declarations: {len(result)}")
    if args.tcslib_only:
        print("(TCSlib only)")
    print()

    by_module: dict[str, list] = {}
    for name, info in result.items():
        by_module.setdefault(info["module"], []).append((info["startLine"], name))

    for module in sorted(by_module):
        entries = sorted(by_module[module])
        print(f"  [{module}]")
        for _, name in entries:
            print(f"    {name}")


def cmd_list(args, graph):
    module = args.module
    if module not in graph:
        # Try prefix match
        matches = [m for m in graph if m.endswith(module) or module in m]
        if not matches:
            print(f"Module not found: {module}")
            return
        module = matches[0]
        print(f"Using: {module}")

    mdata = graph[module]
    print(f"Module: {module}")
    print(f"Direct imports: {len(mdata['directImports'])}")
    print(f"Declarations ({len(mdata['declarations'])}):")
    for name, ddata in sorted(mdata["declarations"].items(), key=lambda x: x[1]["startLine"]):
        ndeps = len(ddata["deps"])
        print(f"  {ddata['startLine']:4d}-{ddata['endLine']:4d}  {name}  ({ndeps} direct deps)")


def cmd_find(args, graph):
    decls = all_declarations(graph)
    matches = find_decl(args.name, decls)
    if not matches:
        print(f"Not found: {args.name}")
        return
    for m in matches:
        info = decls[m]
        print(f"{m}")
        print(f"  module:  {info['module']}")
        print(f"  lines:   {info['startLine']}-{info['endLine']}")
        print(f"  deps:    {len(info['deps'])}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--graph", default=str(DEP_GRAPH), help="Path to dep_graph.json")
    sub = parser.add_subparsers(dest="cmd")

    p_up = sub.add_parser("upstream", help="Show transitive upstream declarations")
    p_up.add_argument("name", help="Declaration name (short or fully-qualified)")
    p_up.add_argument("--tcslib-only", action="store_true", help="Only include TCSlib declarations")

    p_list = sub.add_parser("list", help="List declarations in a module")
    p_list.add_argument("module", help="Module name")

    p_find = sub.add_parser("find", help="Find which module defines a declaration")
    p_find.add_argument("name", help="Declaration name")

    args = parser.parse_args()
    if not args.cmd:
        parser.print_help()
        return

    graph = load_graph(Path(args.graph))

    if args.cmd == "upstream":
        cmd_upstream(args, graph)
    elif args.cmd == "list":
        cmd_list(args, graph)
    elif args.cmd == "find":
        cmd_find(args, graph)


if __name__ == "__main__":
    main()
