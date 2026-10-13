"""Build an elaboration harness: the proposed files' bodies concatenated in dependency order,
under the union of their imports minus the proposed (not yet built) modules.
Usage: mkharness.py OUT FILE... (dependencies first, target last).
Asserts that every body appears verbatim in the harness, and prints SHA-256 sums."""
import sys, hashlib, pathlib
PROPOSED = {"TCSlib.Complexity.FormulaKit.Gate", "TCSlib.Complexity.FormulaKit.Emit",
            "TCSlib.Complexity.FormulaKit"}
out = pathlib.Path(sys.argv[1]); files = [pathlib.Path(p) for p in sys.argv[2:]]
def split(text):
    lines = text.split('\n')
    assert lines[0].startswith('/-'), "copyright block first"
    k = next(i for i, l in enumerate(lines) if l.strip() == '-/')
    head = lines[:k + 1]
    m = k + 1
    imps = []
    while m < len(lines) and (lines[m].startswith('import ') or lines[m].strip() == ''):
        if lines[m].startswith('import '):
            imps.append(lines[m].split()[1])
        m += 1
    return head, imps, '\n'.join(lines[m:])
parts = [split(f.read_text(encoding='utf-8')) for f in files]
imports = []
for _, imps, _ in parts:
    for i in imps:
        if i not in PROPOSED and i not in imports:
            imports.append(i)
head = parts[-1][0]
chunks = ['\n'.join(head), ''] + ['import ' + i for i in imports] + ['']
for f, (_, _, body) in zip(files, parts):
    chunks.append(f'-- ===== RD-2 harness: body of {f.name}, verbatim =====')
    chunks.append(body)
h = '\n'.join(chunks)
for f, (_, _, body) in zip(files, parts):
    assert body in h, f
out.write_text(h, encoding='utf-8')
for f in files + [out]:
    print(hashlib.sha256(f.read_bytes()).hexdigest(), f.name)
