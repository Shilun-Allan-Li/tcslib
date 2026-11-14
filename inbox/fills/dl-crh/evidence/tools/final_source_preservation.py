#!/usr/bin/env python3
"""Static exact-substring preservation check; no Lean or Lake invocation."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

BASE = "eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9"
ROOT = Path(__file__).resolve().parents[2]
OWNER = "TCSlib/Cryptography/Hashing/FromDiscreteLog.lean"


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


base = git("show", BASE + ":" + OWNER)
final = (ROOT / OWNER).read_text()
pattern = r"(?m)^(?:noncomputable )?(?:def|theorem|lemma|abbrev)\s+([^\s:({]+)"
matches = list(re.finditer(pattern, base))
checks = []
for index, match in enumerate(matches):
    end = matches[index + 1].start() if index + 1 < len(matches) else len(base)
    block = base[match.start():end]
    for delimiter in ["\n/--", "\n/-!", "\nattribute ", "\nend "]:
        if delimiter in block:
            block = block.split(delimiter, 1)[0]
    block = block.rstrip()
    if match[1] == "dlHash_crh":
        checks.append({
            "declaration": match[1],
            "frozen_statement_exact": block.split(":= by", 1)[0] in final,
        })
    else:
        checks.append({
            "declaration": match[1],
            "base_code_exact_substring": block in final,
        })
docstrings = re.findall(r"/--.*?-/", base, re.S)
checks.append({
    "original_decl_docstrings": len(docstrings),
    "all_exact_substrings": all(doc in final for doc in docstrings),
})
files = git("diff", "--name-only", BASE, "--", "*.lean").splitlines()
snapshot = []
for file in files:
    data = (ROOT / file).read_bytes()
    snapshot.append({
        "file": file,
        "lines": len(data.splitlines()),
        "sha256": hashlib.sha256(data).hexdigest(),
    })
print(json.dumps({"base": BASE, "checks": checks, "snapshot": snapshot},
                 ensure_ascii=False, indent=2))
