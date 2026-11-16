"""Run the frozen-statement check and its controls (python3 -I, from the fill checkout root).

Usage: run_headers.py <base-commit> <outdir>
For each owned file: the check base -> working tree, then two controls on mutated copies of
the working-tree file: (1) one character of a target header altered must give exactly one
difference (CHANGED=1, REMOVED=0); (2) one reader deleted must give exactly one removal
(CHANGED=0, REMOVED=1). Also writes the extracted target headers for inspection."""
import re, subprocess, sys
from pathlib import Path
here = Path(__file__).resolve().parent
sys.path.insert(0, str(here))
import frozen_headers as fh
base, out = sys.argv[1], Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
FILES = {
    'TCSlib/Cryptography/Hashing/SIS/Columns.lean':
        ('distAdv_hashColumns_uniform_le', 'N * ((1 / 2) * Real.sqrt', 'N * ((1 / 3) * Real.sqrt',
         'hashColumns_apply'),
    'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean':
        ('uniformKey_uniform_advantage_le', 'P.columns * Regev.extractionError P.lwe := by',
         'P.columns * Regev.extractionError P.lwd := by', 'view_eq'),
}
def run(b, f, label, log):
    p = subprocess.run(['python3', '-I', str(here / 'frozen_headers.py'), str(b), str(f), label],
                       capture_output=True, text=True)
    log.write_text(p.stdout + p.stderr)
    return re.search(r'DIFFERENCES=(\d+) CHANGED=(\d+) REMOVED=(\d+) ORDER=(\w+)', p.stdout)
summary = []
for path, (target, old, new, reader) in FILES.items():
    stem = Path(path).stem
    b = out / f'base_{stem}.lean'
    b.write_text(subprocess.check_output(['git', 'show', f'{base}:{path}'], text=True))
    final = Path(path).read_text()
    m = run(b, path, path, out / f'check_{stem}.txt')
    summary.append(f'CHECK    {path}: DIFFERENCES={m[1]} CHANGED={m[2]} REMOVED={m[3]} '
                   f'ORDER={m[4]} -> {"PASS" if m[1] == "0" else "FAIL"}')
    # Extracted target headers.
    with (out / f'target_headers_{stem}.txt').open('w') as h:
        for item in fh.items(final):
            n, d, hd, body, isd = fh.decl_info(item)
            if isd and n in {i[0] for i in map(fh.decl_info, fh.items(b.read_text()))
                             if i[4] and fh.is_target(i[3])}:
                h.write(f'=== {n}\n{hd}\n')
    # Control 1: one character of a target header.
    assert final.count(old) == 1, (path, old)
    c1 = out / f'control_header_{stem}.lean'
    c1.write_text(final.replace(old, new))
    m = run(b, c1, f'control 1 ({target} header, one character)', out / f'control_header_{stem}.txt')
    ok = (m[1], m[2], m[3]) == ('1', '1', '0')
    summary.append(f'CONTROL1 {path}: DIFFERENCES={m[1]} CHANGED={m[2]} REMOVED={m[3]} '
                   f'-> {"PASS" if ok else "FAIL"} (expected exactly one difference)')
    # Control 2: delete one reader (its docstring and declaration).
    items = fh.items(final)
    victim = [i for i in items if fh.decl_info(i)[0] == reader]
    assert len(victim) == 1
    c2 = out / f'control_reader_{stem}.lean'
    c2.write_text(final.replace(victim[0] + '\n', '', 1))
    m = run(b, c2, f'control 2 ({reader} deleted)', out / f'control_reader_{stem}.txt')
    ok = (m[1], m[2], m[3]) == ('1', '0', '1')
    summary.append(f'CONTROL2 {path}: DIFFERENCES={m[1]} CHANGED={m[2]} REMOVED={m[3]} '
                   f'-> {"PASS" if ok else "FAIL"} (expected exactly one removal)')
(out / 'summary.txt').write_text('\n'.join(summary) + '\n')
print('\n'.join(summary))
