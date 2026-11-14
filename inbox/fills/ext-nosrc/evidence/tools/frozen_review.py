"""Read-only proof-scope review; run only with python3 -I from the fill root.

Reports byte preservation of the original declarations and target statement,
source scope, line counts, explicit admissions and global simp attributes.
Writes only its requested evidence files and never invokes Lean or mutates Git.
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess

spec = importlib.util.spec_from_file_location("ext_nosrc_prepare", "evidence/tools/prepare_rule10.py")
assert spec is not None and spec.loader is not None
prep = importlib.util.module_from_spec(spec)
spec.loader.exec_module(prep)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-prefix", type=Path, default=Path("evidence/logs/frozen-review"))
    args = parser.parse_args()
    file = "TCSlib/Cryptography/Randomness/Extraction.lean"
    base = prep.source(prep.OWNED[0], "base").decode()
    final = prep.source(prep.OWNED[0], "final").decode()
    anchor = "namespace TCSlib.Cryptography.Randomness"
    target_doc = "/-- **Theorem 183.6:"
    old = base[base.index(anchor):base.index(target_doc)].rstrip()
    bs = base.index("theorem not_isExtractor_effSources")
    fs = final.index("theorem not_isExtractor_effSources")
    bsig = base[bs:base.index(":= by", bs)]
    fsig = final[fs:final.index(":= by", fs)]
    bd = base.index(target_doc)
    fd = final.index(target_doc)
    bprose = base[bd:base.index("**Proof sketch**", bd)]
    fprose = final[fd:final.index("**Proof sketch**", fd)]
    paths = [Path(m.replace(".", "/") + ".lean") for m in prep.OWNED]
    masked = {str(p): prep.code_mask(p.read_text()) for p in paths}
    simp = {p: re.findall(r"@\[[^\]]*\bsimp\b[^\]]*\]", text) for p, text in masked.items()}
    admissions = {p: re.findall(r"\b(?:sorry|admit|axiom)\b", text) for p, text in masked.items()}
    counts = {str(p): len(p.read_text().splitlines()) for p in paths}
    diff = subprocess.check_output(["git", "--no-optional-locks", "diff", "--name-only", prep.BASE,
                                    "--", "*.lean"], text=True).splitlines()
    untracked = subprocess.check_output(["git", "--no-optional-locks", "ls-files", "--others",
                                         "--exclude-standard", "--", "TCSlib"], text=True).splitlines()
    source_changes = sorted(set(diff + [p for p in untracked if p.endswith(".lean")]))
    owned = {str(p) for p in paths}
    result = {
        "base": prep.BASE,
        "base_declarations_byte_preserved": final[final.index(anchor):].startswith(old),
        "target_signature_byte_preserved": bsig == fsig,
        "target_statement_prose_byte_preserved": bprose == fprose,
        "source_changes": source_changes,
        "scope_pass": set(source_changes).issubset(owned),
        "line_counts": counts,
        "all_below_1000_lines": all(n < 1000 for n in counts.values()),
        "global_simp_attributes": simp,
        "no_new_global_simp_attributes": not any(simp.values()),
        "explicit_admissions": admissions,
        "no_explicit_admissions": not any(admissions.values()),
        "source_hashes": {str(p): prep.digest(p.read_bytes()) for p in paths},
        "tool_sha256": prep.digest(Path(__file__).read_bytes()),
        "prepare_tool_sha256": prep.digest(Path("evidence/tools/prepare_rule10.py").read_bytes()),
        "limitations": "Textual byte/scope checks supplement the Lean axiom census and seals; edge-case correctness was reviewed mathematically, not inferred from this script.",
    }
    keys = ["base_declarations_byte_preserved", "target_signature_byte_preserved",
            "target_statement_prose_byte_preserved", "scope_pass", "all_below_1000_lines",
            "no_new_global_simp_attributes", "no_explicit_admissions"]
    result["all_checks_pass"] = all(result[k] for k in keys)
    rendered = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    prep.write_new(Path(str(args.out_prefix) + ".json"), rendered.encode())
    prep.write_new(Path(str(args.out_prefix) + ".log"), rendered.encode())
    print(rendered, end="")
    if not result["all_checks_pass"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
