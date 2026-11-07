"""Compare each supplemental failing declaration's code with the checked base; python3 -I."""
from pathlib import Path
import ast
import hashlib
import json
import re
import subprocess

root = Path.cwd()
gate = root / "briefs/pass-shelat-ch5-8/gates/08-shared"
out = gate / "evidence-r2"
base = (out / "BASE.txt").read_text().strip()
head = (out / "HEAD.txt").read_text().strip()
summary = json.loads((out / "conservative-summary.json").read_text())
assert summary["head"] == head
# Reuse exactly the existing comment stripper without executing its CLI entry point.
tree = ast.parse((root / "briefs/pass-shelat-ch5-8/maintainer/tools/codeonly.py").read_text())
strip_def = next(node for node in tree.body if isinstance(node, ast.FunctionDef) and node.name == "strip")
scope = {}
exec(compile(ast.Module(body=[strip_def], type_ignores=[]), "codeonly.py:strip", "exec"), scope)
strip = scope["strip"]
decl = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|instance|structure|inductive|abbrev|class|example)\s*([^\s(:{\[]*)")


def blocks(source):
    lines = source.splitlines()
    starts = [(i, m.group(1)) for i, line in enumerate(lines) if (m := decl.match(line))]
    result = []
    for (start, name), (end, _) in zip(starts, starts[1:] + [(len(lines), "")]):
        code = strip("\n".join(lines[start:end])).splitlines()
        # A removed following declaration can expose the outer `end` in this chunk.
        cut = next((i for i, line in enumerate(code[1:], 1)
                    if re.match(r"^(?:namespace|end|section|open|attribute|set_option|run_cmd)\b|^#", line)), len(code))
        result.append((name, start + 1, "\n".join(code[:cut])))
    return result


results = []
for row in summary["seal_results"]:
    module = row["module"]
    path = module.replace(".", "/") + ".lean"
    stem = Path(path).stem
    prefix = summary["probe_prefix"]
    probe = (out / "conservative" / (prefix + stem + ".source.txt")).read_text()
    seal_end = probe.splitlines().index("-- END IMPORT-CLOSURE SEAL") + 1
    log = (out / "logs" / (prefix + stem + ".log")).read_text()
    error_lines = [int(n) for n in re.findall(r"\.lean:(\d+):\d+: error", log)]
    assert len(error_lines) == row["diagnostics"]
    assert all(n > seal_end for n in error_lines), (module, error_lines, seal_end)
    a = blocks(subprocess.check_output(["git", "show", base + ":" + path], text=True))
    b = blocks(subprocess.check_output(["git", "show", head + ":" + path], text=True))
    for name in row["declarations"]:
        aa = [block for block in a if block[0] == name]
        bb = [block for block in b if block[0] == name]
        assert name and len(aa) == len(bb) == 1, (module, name, len(aa), len(bb))
        same = aa[0][2] == bb[0][2]
        results.append({"module": module, "declaration": name, "base_line": aa[0][1],
                        "head_line": bb[0][1], "comment_stripped_block_identical": same,
                        "base_code_sha256": hashlib.sha256(aa[0][2].encode()).hexdigest(),
                        "head_code_sha256": hashlib.sha256(bb[0][2].encode()).hexdigest()})
result = {"base": base, "head": head, "failing_declarations": len(results),
          "all_comment_stripped_blocks_identical": all(row["comment_stripped_block_identical"] for row in results),
          "seal_commands_no_diagnostics": True, "base_seal_rerun": False, "results": results}
(out / "conservative-failure-preservation.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps(result, indent=2))
