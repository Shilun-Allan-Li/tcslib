"""Read-only comparison of exact Git source blobs using the standing freeze parser."""
from pathlib import Path
import collections
import hashlib
import json
import re
import subprocess
import sys

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
CONTEXT = json.loads((OUT / "context.json").read_text())
parser = ROOT / "devtools/seyoon/declfreeze.py"
namespace = {}
exec(compile(parser.read_text().split("\na = chunks(", 1)[0], str(parser), "exec"), namespace)
chunks, statement = namespace["chunks"], namespace["stmt"]
sources = []
all_changed = []
for owner in (OUT / "original9-owners.txt").read_text().splitlines():
    rel = owner.replace(".", "/") + ".lean.txt"
    paths = {label: OUT / "source" / label / rel for label in ["base", "head"]}
    texts = {label: p.read_text() for label, p in paths.items()}
    parsed = {label: {n: dict(private=private, text=text) for n, private, text in chunks(data)}
              for label, data in texts.items()}
    a, b = parsed["base"], parsed["head"]
    common = set(a) & set(b)
    changed = sorted(n for n in common if a[n]["text"] != b[n]["text"])
    public_a = {n for n in a if not a[n]["private"]}
    public_b = {n for n in b if not b[n]["private"]}
    headers = sorted(n for n in common if statement(a[n]["text"]) != statement(b[n]["text"]))
    visibility = sorted(n for n in common if a[n]["private"] != b[n]["private"])
    executable_changed = []
    for n in changed:
        for row in [a[n], b[n]]:
            bare = row["text"].split("-/", 1)[1] if row["text"].startswith("/--") else row["text"]
            if re.search(r"(?m)^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*(?:def|abbrev|instance|structure|inductive|class)\b", bare):
                executable_changed.append(n)
                break
    result = dict(owner=owner, source_equal=texts["base"] == texts["head"],
                  source_sha256={label: hashlib.sha256(p.read_bytes()).hexdigest() for label, p in paths.items()},
                  declaration_counts={label: dict(total=len(rows), public=sum(not r["private"] for r in rows.values()),
                                                    private=sum(r["private"] for r in rows.values())) for label, rows in parsed.items()},
                  public_added=sorted(public_b-public_a), public_removed=sorted(public_a-public_b),
                  private_added=sorted((set(b)-set(a))-public_b), private_removed=sorted((set(a)-set(b))-public_a),
                  statement_changes=headers, visibility_changes=visibility,
                  changed_declarations=changed, executable_chunks_changed=executable_changed,
                  imports={label: re.findall(r"(?m)^import\s+(\S+)", data) for label, data in texts.items()})
    sources.append(result)
    all_changed.extend(dict(owner=owner, name=n, private=a[n]["private"],
                            header_equal=n not in headers, executable=n in executable_changed) for n in changed)
    log = OUT / "source-freeze" / (owner + ".out")
    log.parent.mkdir(exist_ok=True)
    command = [sys.executable, "-I", str(parser), str(paths["base"]), str(paths["head"])]
    run = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert run.returncode == 0
    log.write_bytes(run.stdout)
summary = dict(base=CONTEXT["base"], head=CONTEXT["head"], owners=sources, changed_declarations=all_changed,
               source_diff_files=CONTEXT["changed_Lean_files"],
               parser=dict(path=str(parser), sha256=hashlib.sha256(parser.read_bytes()).hexdigest()),
               limits="Standing lexical declaration parser; exact Git blobs and patch retained. Native raw compiled type/value/attributes are an independent comparison. No private-ID normalization.")
(OUT / "source-freeze.json").write_text(json.dumps(summary, indent=2) + "\n")
print(json.dumps(dict(changed_declaration_count=len(all_changed),
                      owners=[{k:r[k] for k in ["owner", "source_equal", "public_added", "public_removed", "private_added", "private_removed", "statement_changes", "visibility_changes", "executable_chunks_changed"]} for r in sources]),indent=2))
