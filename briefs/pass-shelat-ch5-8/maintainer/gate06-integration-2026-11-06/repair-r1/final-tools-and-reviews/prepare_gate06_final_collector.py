"""Prepare only the fresh final collector: BASE_SHA HEAD_SHA; never starts Lean."""
from pathlib import Path
import argparse, ast, hashlib, importlib.util, json, os, re, subprocess, sys

ROOT = Path("/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4")
G06 = ROOT / ".lake/ps-maintainer/gate06"
EVIDENCE = Path("/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1")
SCRATCH_REL = Path(".lake/ps-maintainer/gate06/rule10-final-r1")
SHARED = ROOT / "briefs/pass-shelat-ch5-8/gates/08-shared/evidence/tools"
TOOL_PATHS = {"build_seals.py": G06 / "build_seals.py", "build_controls.py": G06 / "build_controls.py",
    "request_payload_adapter.py": G06 / "repairs/prepare_rule10_harness_retry_v3.py",
    "prepare_audit.py": G06 / "prepare_audit.py", "touched.py": SHARED / "touched.py",
    "collect_body.lean": SHARED / "collect_body.lean", "check_probe_v2.py": G06 / "check_probe_v2.py"}
TOOL_HASHES = {"build_seals.py": "fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a",
    "build_controls.py": "484009543d095685b50fea244427adf4907de11bd5ef6a9e17e76fe08c60cf89",
    "request_payload_adapter.py": "ae79f1ec66e93c8bc7749a53e12e3d383feda020ad2978520a0cfa24b12eb5de",
    "prepare_audit.py": "055e652d9769044d757960586a94f4feffe78a942ca2d9555f02db9dccfa258f",
    "touched.py": "95d47b5541adcf4670120ab761890a2be899c3f1e77e367a459cac7ad96ffe97",
    "collect_body.lean": "751aa8f8385a05690a0a0097acaff6d93e7349067b5e16a5a59662db0cafb57b",
    "check_probe_v2.py": "5048912fda9ecd1eb6dd9a238d94bfd73d55a70e9e7d2c4a2df75bfda7e9d146"}

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def encoded(value):
    return (json.dumps(value, indent=2, ensure_ascii=False) + "\n").encode()

def tool_bytes():
    raw = {}
    for name, path in TOOL_PATHS.items():
        need(path.is_file() and not path.is_symlink(), "nonordinary tool: " + str(path))
        raw[name] = path.read_bytes()
        need(sha(raw[name]) == TOOL_HASHES[name], "reviewed tool changed: " + name)
    return raw

def saved_tool_name(name):
    return name + ".source.txt" if name.endswith(".lean") else name

def load_tool(name, module_name):
    need(sha(TOOL_PATHS[name].read_bytes()) == TOOL_HASHES[name], "tool changed: " + name)
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location(module_name, TOOL_PATHS[name])
    need(spec is not None and spec.loader is not None, "cannot load tool: " + name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module

def derive_scope(bs, library, base, head):
    changed = bs.git(ROOT, "diff", "--name-only", base, head, "--", "*.lean").decode().splitlines()
    need(len(set(changed)) == len(changed) and all(p in library for p in changed), "unsupported/deleted/nonlibrary Lean path")
    modules, excluded = {}, []
    for path in sorted(changed):
        info = bs.header(library[path])
        if bs.DECL_RE.search(info["code"]):
            need(path.startswith("TCSlib/"), "math declaration outside the library namespace tree")
            modules[path[:-5].replace("/", ".")] = path
        else:
            active = [s.strip() for s in info["code"].splitlines() if s.strip()]
            need(all(bs.IMPORT_RE.fullmatch(s) or re.fullmatch(r"set_option\s+\S+\s+\S+", s) for s in active), "excluded file is not import/option-only: " + path)
            excluded.append(path)
    need(modules, "no audited math modules")
    def imports(module):
        path = module.replace(".", "/") + ".lean"
        need(path in library, "missing TCSlib import: " + module)
        return [m for m in bs.header(library[path])["imports"] if m == "TCSlib" or m.startswith("TCSlib.")]
    closures = {}
    for module in modules:
        found, stack = set(), imports(module)
        while stack:
            dep = stack.pop()
            if dep not in found:
                found.add(dep); stack.extend(imports(dep))
        need(module not in found, "self/cyclic import closure: " + module)
        closures[module] = sorted(found)
    return modules, closures, {p: sha(library[p]) for p in changed}, excluded

def collector_source(raw_tools, modules, closures):
    body = raw_tools["collect_body.lean"].decode()
    edits = [("ts.any fun t => s == t", 'ts.any fun t => t == "*" || s == t'),
        ("for t in ts do\n    unless ours.any", 'for t in ts do\n    if t == "*" then continue\n    unless ours.any'),
        ("if s == t || s.endsWith", 'if t == "*" || s == t || s.endsWith')]
    ax = 'logInfo m!"AXIOMS {modN} | {s} | {axs.toList}"'
    edits.append((ax, ax + '\n          logInfo m!"AXIOMSID {modN} | {n.toString} | display={s} | {axs.toList}"'))
    for old, new in edits:
        need(body.count(old) == 1, "collector wildcard/axiom anchor differs")
        body = body.replace(old, new)
    values = [n.value for n in ast.parse(raw_tools["prepare_audit.py"]).body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "closure_body" for t in n.targets)]
    need(len(values) == 1, "closure supplement literal missing")
    closure_body = ast.literal_eval(values[0])
    source = "\n".join(["import Lean", *("import " + m for m in modules), "set_option maxHeartbeats 0", body, closure_body]) + "\n"
    for module in modules:
        source += '#collect ' + module + ' ["*"]\n#axs ' + module + ' ["*"]\n'
        source += '#sealclosure ' + module + ' [' + ', '.join(closures[module]) + ']\n'
    return source.encode()

def write_new(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("xb") as handle:
        handle.write(raw)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("base"); parser.add_argument("head"); args = parser.parse_args()
    need(all(re.fullmatch(r"[0-9a-f]{40}", v) for v in (args.base, args.head)), "base/head must be full lowercase commit SHAs")
    need(not EVIDENCE.exists() and not (ROOT / SCRATCH_REL).exists(), "refusing existing final evidence/scratch root")
    raw_tools = tool_bytes(); bs = load_tool("build_seals.py", "gate06_final_source_builder")
    for value in (args.base, args.head):
        need(bs.git(ROOT, "rev-parse", value + "^{commit}").decode().strip() == value, "commit does not resolve exactly")
    pins = {"base": args.base, "head": args.head, "base_is_ancestor": True, "library_sources_equal_head": True,
        "untracked_or_ignored_library_lean_files": 0, "library_git_tree": bs.git(ROOT, "rev-parse", args.head + ":TCSlib").decode().strip()}
    library, snapshot = bs.library_snapshot(ROOT, pins)
    modules, closures, fingerprints, excluded = derive_scope(bs, library, args.base, args.head)
    pins.update({"changed_lean_files": len(fingerprints), "audited_math_modules": len(modules),
        "excluded_import_option_only_files": excluded,
        "collector_scope": "all stored constants, types/values/private/generated, plus complete current import-closure supplement",
        "anonymous_limit": "anonymous commands require the complete closure supplement and anonymous control"})
    env = {**os.environ, "GIT_OPTIONAL_LOCKS": "0"}
    touched = {m: subprocess.check_output([sys.executable, "-I", str(TOOL_PATHS["touched.py"]), str(ROOT), args.base, path], env=env, text=True).splitlines() for m, path in modules.items()}
    bs.EXPECTED_MODULES = len(modules); bs.SCRATCH_REL = SCRATCH_REL
    bs.validate_metadata(ROOT, pins, modules, closures, fingerprints, touched, library)
    source = collector_source(raw_tools, modules, closures)
    data = {"pins.json": encoded(pins), "modules.json": encoded(modules), "closures.json": encoded(closures),
        "source-fingerprints.json": encoded(fingerprints), "touched.json": encoded(touched), "Collect.source.txt": source}
    self_raw = Path(__file__).read_bytes()
    prep = {"status": "COLLECTOR_PREPARED_NOT_RUN", "root": str(ROOT), "evidence_directory": str(EVIDENCE),
        "base": args.base, "head": args.head, "scratch_relative": SCRATCH_REL.as_posix(),
        "expected_math_modules": len(modules), "modules": sorted(modules), "library_verification": snapshot,
        "input_sha256": {n: sha(b) for n, b in data.items()}, "tool_input_sha256": TOOL_HASHES,
        "tool_saved_names": {name: saved_tool_name(name) for name in raw_tools},
        "preparer_source_sha256": sha(self_raw), "collector_module": (SCRATCH_REL / "Collect").as_posix(), "collector_label": "collect1",
        "limit": "Preparation only; root must reconcile current native prerequisites and run fresh collection before seal/control preparation."}
    need(bs.library_snapshot(ROOT, pins) == (library, snapshot) and tool_bytes() == raw_tools, "sources/tools changed during preparation")
    EVIDENCE.mkdir(parents=True, exist_ok=False); (ROOT / SCRATCH_REL).mkdir(parents=True, exist_ok=False)
    for name, raw in data.items(): write_new(EVIDENCE / name, raw)
    for name, raw in raw_tools.items(): write_new(EVIDENCE / "tool-inputs" / saved_tool_name(name), raw)
    write_new(ROOT / SCRATCH_REL / "Collect.lean", source)
    write_new(EVIDENCE / "prepare_gate06_final_collector.py", self_raw)
    write_new(EVIDENCE / "final-preparation.json", encoded(prep))
    command = [sys.executable, "-I", str(TOOL_PATHS["check_probe_v2.py"]), str(EVIDENCE), prep["collector_module"], "collect1"]
    print(json.dumps({"status": prep["status"], "modules": len(modules), "collector_cwd": str(ROOT), "collector_command": command}), flush=True)

if __name__ == "__main__":
    main()
