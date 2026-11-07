"""Expanded collector, whole-file seals and controls after bootstrap; python3 -I at record root."""
from pathlib import Path
import datetime
import json
import os
import re
import subprocess
import sys

root = Path.cwd()
wt = Path("/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4")
gate = root / "briefs/pass-shelat-ch5-8/gates/08-shared"
out = gate / "evidence-r2"
logs = out / "logs"
scratch = root / ".lake/ps-maintainer/gate08-r2"
env = os.environ.copy()
copied = json.loads((out / "copied-tree.json").read_text())
assert copied["rebuilt_verified"]
assert copied["head"] == (out / "HEAD.txt").read_text().strip()
required = {path[:-5] for path in (out / "source-targets.txt").read_text().splitlines()}
assert required <= {row["module"] for row in copied["modules"]}
env["TCSLIB_OLEANS"] = copied["target"]
assert subprocess.check_output(["git", "-C", str(wt), "rev-parse", "HEAD"], text=True).strip() == \
    (out / "HEAD.txt").read_text().strip()


def check(module, name):
    log = logs / name
    # Resume only completed checks in this pinned run, with their exact saved probe source.
    if log.exists():
        stem = module.rsplit("/", 1)[1]
        saved = out / "seal" / (stem + ".source.txt") if name.startswith("sealed-") else out / (stem + ".source.txt")
        text = log.read_text()
        ended = re.search(r"(?m)^END .+ RC (-?\d+)$", text)
        if ended and saved.exists():
            assert (root / (module + ".lean")).read_bytes() == saved.read_bytes()
            rc = int(ended.group(1))
            print(module + f" rc={rc} (completed pinned check retained)", flush=True)
            return rc, text
    with log.open("w") as handle:
        handle.write("START " + datetime.datetime.now(datetime.timezone.utc).isoformat() + "\n")
        handle.flush()
        p = subprocess.Popen(
            ["/usr/bin/time", "-l", "bash", "scripts/lean_check_tree.sh", module],
            stdout=handle, stderr=subprocess.STDOUT, env=env, cwd=root)
        (logs / "checks.pid").write_text(str(p.pid) + "\n")
        rc = p.wait()
        handle.write("\nEND " + datetime.datetime.now(datetime.timezone.utc).isoformat() + f" RC {rc}\n")
    print(module + f" rc={rc}", flush=True)
    return rc, log.read_text()


prefix = ".lake/ps-maintainer/gate08-r2/"
rc, collected = check(prefix + "CollectExpanded", "collect-expanded.log")
assert rc == 0
assert "TOUCHED-NOT-FOUND" not in collected and "AXIOMS-NOT-FOUND" not in collected
names = {}
for module, name in re.findall(r"SEALROW (\S+) \| (\S+) \|", collected):
    if name not in {"Complexity.PolyExpr.eval", "TCSlib.Cryptography.glNeed"}:
        names.setdefault(module, set()).add(name)
targets = (out / "source-targets.txt").read_text().splitlines()
modules = {path[:-5].replace("/", "."): path for path in targets}
for module in modules:
    names.setdefault(module, set())
assert set(names) == set(modules)
union = set().union(*names.values())
(out / "seal").mkdir(exist_ok=True)
additions = []
for module, path in modules.items():
    stem = Path(path).stem
    old = {line.strip() for line in (gate / "evidence/seal" / f"names-{stem}.txt").read_text().splitlines() if line.strip()}
    assert old <= names[module], (module, old - names[module])
    additions.extend((module, name) for name in sorted(names[module] - old))
    (out / "seal" / f"names-{stem}.txt").write_text("\n".join(sorted(names[module])) + "\n")
(out / "seal/names-ALL.txt").write_text("\n".join(sorted(union)) + "\n")
axioms = re.findall(r"AXIOMS (\S+) \| (\S+) \| \[([^\]]*)\]", collected)
assert len(axioms) == 146, len(axioms)
for _, name, printed in axioms:
    actual = {part.strip() for part in printed.split(",") if part.strip()}
    permitted = {"propext", "Classical.choice", "Quot.sound"}
    if name.endswith(".polyTimeComputable_rejectBlocksL"):
        permitted.add("sorryAx")
    assert actual <= permitted, (name, actual)

sorry_names = [name for _, name, axioms_ in axioms if "sorryAx" in axioms_]
assert sorry_names == ["TCSlib.Cryptography.Candidates.polyTimeComputable_rejectBlocksL"], sorry_names
(out / "axioms-touched.tsv").write_text("\n".join("\t".join(row) for row in axioms) + "\n")

expected = {
    "Concrete": {"primesPairEquiv_apply_val"},
    "DiscreteLog": {"ExpGroupGen.FullLength.exists_fullLengthExcept"},
    "Rabin": {"rabinCollection_index", "rabinBlumTrapdoor_index"},
    "Basic": {"uexp_mono"},
    "Factoring": {"exists_plantFactorer"},
}
seal_results = []
for module, path in modules.items():
    stem = Path(path).stem
    probe = scratch / f"Sealed{stem}.lean"
    nf = out / "seal" / f"names-{stem}.txt"
    subprocess.run(["python3", "-I", str(gate / "evidence/tools/mkseal.py"),
                    str(wt / path), str(probe), str(nf)], check=True, capture_output=True, text=True)
    (out / "seal" / f"Sealed{stem}.source.txt").write_bytes(probe.read_bytes())
    rc, text = check(prefix + "Sealed" + stem, f"sealed-{stem}.log")
    details = subprocess.check_output([
        "python3", "-I", str(gate / "evidence/tools/errdecl.py"), str(probe),
        str(logs / f"sealed-{stem}.log"),
        str(gate / "evidence/seal" / f"touched-{stem}.txt")], text=True)
    failures = set(re.findall(r"decl `([^`]+)`", details))
    assert failures == expected.get(stem, set()), (stem, failures, details)
    assert "touched=True" not in details, details
    assert (rc == 0) == (not failures), (stem, rc, failures)
    (out / "seal" / f"Sealed{stem}.errors.txt").write_text(details)
    seal_results.append({"module": module, "rc": rc, "untouched_failures": sorted(failures)})

imports = "\n".join(line for line in (out / "CollectExpanded.source.txt").read_text().splitlines()
                    if line.startswith("import "))
body = (gate / "evidence/tools/controls_body.lean").read_text()
extra = """
namespace S1PrimeControl
example (w : List Bool) : primeStr w = [decide (listToNat w).Prime] := rfl
end S1PrimeControl
"""
plain = imports + "\n" + body + extra
sealed = imports + "\nattribute [local irreducible] " + " ".join(sorted(union)) + "\n" + body + extra
for name, source in [("ControlsUnsealed", plain), ("ControlsSealed", sealed)]:
    (scratch / (name + ".lean")).write_text(source)
    (out / (name + ".source.txt")).write_text(source)
    rc, text = check(prefix + name, name + ".log")
    errors = len(re.findall(r"\.lean:\d+:\d+: error:", text))
    assert (rc == 0 and errors == 0) if name.endswith("Unsealed") else (rc != 0 and errors == 14), \
        (name, rc, errors)

result = {
    "head": (out / "HEAD.txt").read_text().strip(),
    "unique_names": len(union), "added_pairs": additions,
    "touched_axiom_prints": len(axioms), "touched_sorry_names": sorry_names,
    "seal_results": seal_results, "touched_failures": 0,
    "controls_unsealed_passed": 14, "controls_sealed_failed": 14,
    "original_base_controls_rerun": False,
}
(out / "expanded-checks-summary.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({key: value for key, value in result.items() if key != "seal_results"}), flush=True)
