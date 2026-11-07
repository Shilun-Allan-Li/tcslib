"""Import-closure supplemental seals; run as python3 -I from the records root."""
from pathlib import Path
import datetime
import json
import os
import re
import subprocess

root = Path.cwd()
gate = root / "briefs/pass-shelat-ch5-8/gates/08-shared"
out = gate / "evidence-r2"
wt = Path("/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4")
head = (out / "HEAD.txt").read_text().strip()
assert subprocess.check_output(["git", "-C", str(wt), "rev-parse", "HEAD"], text=True).strip() == head
copied = json.loads((out / "copied-tree.json").read_text())
assert copied["rebuilt_verified"] and copied["head"] == head
env = os.environ.copy()
env["TCSLIB_OLEANS"] = copied["target"]
scratch = root / ".lake/ps-maintainer/gate08-r2"
data = out / "conservative"
data.mkdir(exist_ok=True)


def check(stem, source):
    probe = scratch / (stem + ".lean")
    saved = data / (stem + ".source.txt")
    log = out / "logs" / (stem + ".log")
    if log.exists() and saved.exists():
        previous = log.read_text()
        ended = re.search(r"(?m)^END .+ RC (-?\d+)$", previous)
        if ended:
            assert saved.read_text() == source and probe.read_text() == source
            rc = int(ended.group(1))
            print(stem + f" rc={rc} (completed pinned check retained)", flush=True)
            return rc, previous
    probe.write_text(source)
    saved.write_text(source)
    with log.open("w") as handle:
        handle.write("START " + datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n")
        handle.flush()
        rc = subprocess.run(["/usr/bin/time", "-l", "bash", "scripts/lean_check_tree.sh",
                             str(probe.relative_to(root))[:-5]], cwd=root, env=env,
                            stdout=handle, stderr=subprocess.STDOUT).returncode
        handle.write("\nEND " + datetime.datetime.now(datetime.timezone.utc).isoformat() + f" RC {rc}\n")
    print(stem + f" rc={rc}", flush=True)
    return rc, log.read_text()


def imports(module):
    source = (wt / (module.replace(".", "/") + ".lean")).read_text()
    return [m for m in re.findall(r"(?m)^import\s+(\S+)", source) if m.startswith("TCSlib.")]


def closure(module):
    found = set()
    stack = imports(module)
    while stack:
        item = stack.pop()
        if item not in found:
            found.add(item)
            stack.extend(imports(item))
    return sorted(found)


targets = (out / "source-targets.txt").read_text().splitlines()
modules = {path[:-5].replace("/", "."): path for path in targets}
closures = {module: closure(module) for module in modules}
(data / "import-closures.json").write_text(json.dumps(closures, indent=2) + "\n")
imports_source = "\n".join(line for line in (out / "CollectExpanded.source.txt").read_text().splitlines()
                           if line.startswith("import "))
collector = r'''
open Lean Meta Elab Command
syntax (name := closureSealCmd) "#sealclosure " ident "[" ident,* "]" : command
@[command_elab closureSealCmd] def closureSeal : CommandElab := fun stx => do
  let audited := stx[1].getId
  let deps := stx[3].getSepArgs.map Syntax.getId
  let env ← getEnv
  for dep in deps do
    unless (env.getModuleIdx? dep).isSome do throwError "missing dependency {dep}"
  let mut rows : Array String := #[]
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let home := env.header.moduleNames[mi.toNat]!
    unless deps.contains home do continue
    unless ci.isDefinition do continue
    if isInstanceCore env n then continue
    let matcher := (Match.Extension.getMatcherInfo? env n).isSome
    let status ← liftCoreM <| getReducibilityStatus n
    if !matcher && status == .reducible then continue
    if n == `Complexity.PolyExpr.eval || n == `TCSlib.Cryptography.glNeed then continue
    rows := rows.push s!"CLOSUREROW {audited} | {n} | {home}"
  for row in rows.qsort (· < ·) do logInfo m!"{row}"
'''
commands = "\n".join("#sealclosure " + module + " [" + ", ".join(deps) + "]"
                     for module, deps in closures.items())
rc, collected = check("CollectConservative", imports_source + "\n" + collector + commands + "\n")
assert rc == 0
names = {module: set() for module in modules}
for module, name in re.findall(r"CLOSUREROW (\S+) \| (\S+) \|", collected):
    names[module].add(name)

results = []
for module, path in modules.items():
    stem = Path(path).stem
    nf = data / ("names-" + stem + ".txt")
    nf.write_text("\n".join(sorted(names[module])) + "\n")
    small = {line for line in (out / "seal" / ("names-" + stem + ".txt")).read_text().splitlines() if line}
    assert small <= names[module], (module, small - names[module])
    probe = scratch / ("ClosureVerified" + stem + ".lean")
    source_lines = (wt / path).read_text().split("\n")
    i = next(k for k, line in enumerate(source_lines) if line.startswith("namespace "))
    j = i + 1
    while j < len(source_lines) and not source_lines[j].strip():
        j += 1
    insert = j if source_lines[j].startswith("open ") else i
    # Resolve printed names against the environment, including numerical/hygienic components.
    spellings = json.dumps(sorted(names[module]), ensure_ascii=False)
    seal = '''-- Import-closure seal, independent of stored-constant reads.
run_cmd do
  let env ← Lean.getEnv
  let mut catalog : Std.HashMap String (Array Lean.Name) := {}
  let mut active : Nat := 0
  let mut already : Nat := 0
  for (n, _) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    unless (`TCSlib).isPrefixOf env.header.moduleNames[mi.toNat]! do continue
    let ns := (catalog[n.toString]?).getD #[]
    catalog := catalog.insert n.toString (ns.push n)
  for spelling in (#''' + spellings + ''' : Array String) do
    let ns := (catalog[spelling]?).getD #[]
    unless ns.size == 1 do throwError "seal name not found or ambiguous: {spelling}"
    let n := ns[0]!
    let before ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if before == .irreducible then
      already := already + 1
    else
      let id := Lean.mkIdent n
      Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $id:ident))
      active := active + 1
    let status ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless status == .irreducible do throwError "seal not installed: {n}"
  Lean.logInfo m!"SUPPLEMENT-SEAL active={active} already={already}"
-- END IMPORT-CLOSURE SEAL
'''
    source_lines.insert(insert + 1, seal)
    source = "\n".join(source_lines)
    rc, text = check("ClosureVerified" + stem, source)
    assert not re.search(r"unknownIdentifier|unexpected token|seal name not found|seal not installed", text), text
    seal_end = source.splitlines().index("-- END IMPORT-CLOSURE SEAL") + 1
    error_lines = [int(n) for n in re.findall(r"\.lean:(\d+):\d+: error", text)]
    assert all(n > seal_end for n in error_lines), (module, error_lines, seal_end)
    counts = re.findall(r"SUPPLEMENT-SEAL active=(\d+) already=(\d+)", text)
    assert len(counts) == 1 and sum(map(int, counts[0])) == len(names[module])
    details = subprocess.check_output(["python3", "-I", str(gate / "evidence/tools/errdecl.py"),
                                      str(probe), str(out / "logs" / ("ClosureVerified" + stem + ".log")),
                                      str(gate / "evidence/seal" / ("touched-" + stem + ".txt"))], text=True)
    (data / (stem + ".errors.txt")).write_text(details)
    results.append({"module": module, "candidate_count": len(names[module]),
                    "active_seals": int(counts[0][0]), "already_irreducible": int(counts[0][1]), "rc": rc,
                    "diagnostics": len(error_lines),
                    "declarations": re.findall(r"decl `([^`]*)`", details),
                    "touched_failure": "touched=True" in details})

# The sole foreign-definition read in this probe is in an anonymous example.
plain = "import TCSlib.Cryptography.Candidates.Concrete\n" + \
        "example (w : List Bool) : TCSlib.Cryptography.Candidates.primeStr w = " + \
        "[decide (TCSlib.Cryptography.NumberTheory.listToNat w).Prime] := rfl\n"
sealed = plain.replace("example (w", "attribute [local irreducible] TCSlib.Cryptography.Candidates.primeStr\nexample (w")
rc_plain, _ = check("AnonymousFinalUnsealed", plain)
rc_sealed, text = check("AnonymousFinalSealed", sealed)
assert rc_plain == 0 and rc_sealed != 0 and len(re.findall(r"\.lean:\d+:\d+: error:", text)) == 1
assert "TCSlib.Cryptography.Candidates.primeStr" in names["TCSlib.Cryptography.Candidates.RSA"]
# Repeat the anonymous-only control with the actual complete RSA import-closure seal.
rsa_lines = (data / "ClosureVerifiedRSA.source.txt").read_text().splitlines()
start = rsa_lines.index("-- Import-closure seal, independent of stored-constant reads.")
end = rsa_lines.index("-- END IMPORT-CLOSURE SEAL") + 1
broad_seal = "\n".join(rsa_lines[start:end]) + "\n"
broad_plain = plain.replace("import TCSlib.Cryptography.Candidates.Concrete", "import TCSlib.Cryptography.Candidates.RSA")
import_line, example = broad_plain.split("\n", 1)
rc_broad_plain, _ = check("AnonymousBroadUnsealed", broad_plain)
rc_broad_sealed, broad_text = check("AnonymousBroadSealed", import_line + "\n" + broad_seal + example)
assert rc_broad_plain == 0 and rc_broad_sealed != 0
assert len(re.findall(r"\.lean:\d+:\d+: error:", broad_text)) == 1
summary = {"head": head, "probe_prefix": "ClosureVerified", "candidate_pairs": sum(map(len, names.values())), "seal_results": results,
           "touched_failures": sum(r["touched_failure"] for r in results),
           "anonymous_only_unsealed_rc": rc_plain, "anonymous_only_sealed_rc": rc_sealed,
           "anonymous_broad_unsealed_rc": rc_broad_plain, "anonymous_broad_sealed_rc": rc_broad_sealed,
           "exclusions": ["instances", "reducible nonmatchers", "Complexity.PolyExpr.eval", "TCSlib.Cryptography.glNeed"]}
(out / "conservative-summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary), flush=True)
