"""Reconcile round-5 records from pinned Git sources; run at the root with python3 -I."""

from collections import Counter
from pathlib import Path
import difflib
import json
import runpy
import subprocess
import sys


root = Path.cwd()
gate = root / "briefs/pass-shelat-ch5-8/gates/04-s2b"
evidence = gate / "evidence-r5"
out = gate / "evidence-r5-review"


def git(*args):
    return subprocess.check_output(["git", *args], cwd=root, text=True)


head = git("rev-parse", "origin/cryptography/pass-shelat-ch5-8-s2b").strip()
base = git("rev-parse", "7018d13e243df4d8b54b99444c34c934199755f5").strip()
round4 = git("rev-parse", "a588adfed01eefe6971abd0846e3938ad02e8624").strip()
old_comparison = git("rev-parse", "849b86b8").strip()
new_comparison = git("rev-parse", "4d99b0cb").strip()
assert head == "9ac1c4260adb8fbfe8c6f50df7786dbdd015656e"

pr_files = git("diff", "--name-only", base, head, "--", "*.lean").splitlines()
implementation_files = (evidence / "pr-files.txt").read_text().splitlines()
modules = (evidence / "tools/mods.txt").read_text().splitlines()
seal_files = [m.replace(".", "/") + ".lean" for m in modules]
assert len(pr_files) == 26 and len(seal_files) == 26
assert set(pr_files) == set(implementation_files) | {"TCSlib.lean"}
filesets = {
    "head": head,
    "pr_base": base,
    "pr_delta": pr_files,
    "implementation_delta": implementation_files,
    "seal_targets": seal_files,
    "seal_only": sorted(set(seal_files) - set(pr_files)),
    "pr_only": sorted(set(pr_files) - set(seal_files)),
    "historical_statement_comparison": [old_comparison, new_comparison],
    "direct_round4_comparison": [round4, head],
}
(out / "file-sets.json").write_text(json.dumps(filesets, indent=2) + "\n")

rows = ["| Seal target | Active pairs | Already irreducible | Notation rows dropped |",
        "|---|---:|---:|---:|"]
active_total = irreducible_total = dropped_total = 0
dropped = (evidence / "candidates/unsealable-dropped.tsv").read_text().splitlines()
for module, path in zip(modules, seal_files):
    lines = (evidence / "candidates" / (module + ".txt")).read_text().splitlines()
    active = sum(bool(line.strip()) and not line.startswith("#") for line in lines)
    irreducible = sum(line.startswith("# already-irreducible: ") for line in lines)
    notation = sum(line.startswith(module + ".txt\t") for line in dropped)
    active_total += active
    irreducible_total += irreducible
    dropped_total += notation
    rows.append(f"| `{path}` | {active} | {irreducible} | {notation} |")
rows.append(f"| **Total** | **{active_total}** | **{irreducible_total}** | **{dropped_total}** |")
assert (active_total, irreducible_total, dropped_total) == (260, 1, 7)
(out / "post-filter-candidates.md").write_text("\n".join(rows) + "\n")

tool = root / "briefs/pass-shelat-ch5-8/maintainer/tools/decls2.py"
saved_argv = sys.argv
sys.argv = [str(tool), str(root), round4]
api = runpy.run_path(str(tool), run_name="gate04_header_api")
sys.argv = saved_argv
decls = api["decls"]
diff_lines = ["# Source-header comparison; not an elaborated-signature check.",
              "# OLD " + round4, "# NEW " + head]
counts = Counter()
for path in pr_files:
    old = decls(git("show", round4 + ":" + path))
    new = decls(git("show", head + ":" + path))
    for name in sorted(set(old) | set(new)):
        kind = "ADDED" if name not in old else "REMOVED" if name not in new else \
            "CHANGED" if old[name][2] != new[name][2] else None
        if kind is None:
            continue
        counts[kind] += 1
        diff_lines.append("\t".join([kind, path, name,
                                      old[name][2] if name in old else "",
                                      new[name][2] if name in new else ""]))
(out / "round4-to-head-headers.tsv").write_text("\n".join(diff_lines) + "\n")

file_list = out / "pr-delta-files.txt"
file_list.write_text("\n".join(pr_files) + "\n")
docdiff = subprocess.check_output([
    "python3", "-I", str(evidence / "tools/stmtdiff.py"), str(root), round4, head,
    str(file_list),
], text=True)
(out / "round4-to-head-docs-and-source-statements.txt").write_text(
    "# Historical source comparator (not elaborated signatures); OLD " + round4 +
    "\n# NEW " + head + "\n" + docdiff)

path = "TCSlib/Cryptography/ZeroKnowledge/Interaction.lean"
source = git("show", head + ":" + path)
updated = source
replacements = [
    ("/-- The defining equation of `transcriptWith`: the execution `exec` on the two tapes. -/",
     "/-- The transcript against `P'` is the execution with the protocol's verifier and first-mover\n"
     "flag, common input `x`, private inputs `y`, `z`, tapes `List.ofFn r.1`, `List.ofFn r.2`,\n"
     "and `π.rounds.eval x.length` moves:\n"
     "`π.transcriptWith P' x y z r = exec P' π.V π.verifierFirst x y z\n"
     "  (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)`. -/"),
    ("/-- The defining equation of `outV`: the verifier's next message on the received messages. -/",
     "/-- The verifier's output is its next message on common input `x`, private input `z`,\n"
     "verifier tape `List.ofFn r.2` and the messages it received:\n"
     "`π.outV P' x y z r = π.V.next x z (List.ofFn r.2)\n"
     "  (π.transcriptWith P' x y z r).2`. -/"),
]
for old, new in replacements:
    assert updated.count(old) == 1
    updated = updated.replace(old, new)
assert api["strip"](source).split() == api["strip"](updated).split()
patch = "".join(difflib.unified_diff(
    source.splitlines(keepends=True), updated.splitlines(keepends=True),
    fromfile="a/" + path, tofile="b/" + path))
(out / "interaction-docstrings.diff").write_text(patch)
summary = {"head": head, "pr_delta_files": len(pr_files), "seal_targets": len(seal_files),
           "active_pairs": active_total, "already_irreducible_pairs": irreducible_total,
           "notation_rows_dropped": dropped_total, "direct_round4_source_headers": dict(counts),
           "docstring_patch_changes_code": False}
(out / "summary.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(summary))
