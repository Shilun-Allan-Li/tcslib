"""Name-clash scan for the gsw-security owned files (python3 -I).

Usage: name_clash.py <base-tree-root> <final-tree-root>
Extracts every declaration (public or private; `theorem`, `lemma`, `def`, `abbrev`,
`structure`, `class`, `inductive`, `instance` with a name) of the two owned files with its
namespace resolved (tracking `namespace X` / `end X`, honouring `_root_.`), at base and at final.
The new names are those at final that are not at base. Each new name is then looked up among
all declarations of every `.lean` file under TCSlib/ in the base tree (namespaces resolved the
same way). Also reports a new name whose last component equals a base declaration's in the same
namespace. Exit 0 iff no new name is already declared at base.
"""
import re
import sys
from pathlib import Path

FILES = ['TCSlib/Cryptography/Hashing/SIS/Columns.lean',
         'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW/Security.lean']
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe)\s+)*'
                  r'(?:theorem|lemma|def|abbrev|structure|class|inductive|instance)\s+'
                  r'([^\s:({\[]+)')


def strip_comments(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)


def declarations(src):
    out, stack = [], []
    for line in strip_comments(src).split('\n'):
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(m[1]); continue
        m = re.match(r'^end\s+(\S+)\s*$', line)
        if m and stack and stack[-1] == m[1]:
            stack.pop(); continue
        m = DECL.match(line)
        if m:
            name = m[1]
            full = name[len('_root_.'):] if name.startswith('_root_.') else \
                '.'.join(stack + [name])
            out.append(full)
    return out


base_root, final_root = Path(sys.argv[1]), Path(sys.argv[2])
base_own = set()
final_own = []
for f in FILES:
    base_own |= set(declarations((base_root / f).read_text()))
    final_own += declarations((final_root / f).read_text())
new = [n for n in final_own if n not in base_own]
index = {}
for path in sorted((base_root / 'TCSlib').rglob('*.lean')):
    for n in declarations(path.read_text()):
        index.setdefault(n, []).append(str(path.relative_to(base_root)))
print(f'owned declarations: base={len(base_own)} final={len(final_own)} new={len(new)}')
print(f'base TCSlib declarations indexed: {sum(map(len, index.values()))} '
      f'({len(index)} distinct names)')
clash = 0
for n in new:
    hits = index.get(n, [])
    print(f'{"CLASH" if hits else "free "} {n}' + (f'  <- {hits}' if hits else ''))
    clash += bool(hits)
dups = [n for n in set(final_own) if final_own.count(n) > 1]
for n in dups:
    print(f'DUPLICATE-IN-OWNED {n}')
print(f'NAME CLASH SCAN: new={len(new)} clashes={clash} duplicates={len(dups)} -> '
      f'{"PASS" if not clash and not dups else "FAIL"}')
sys.exit(1 if clash or dups else 0)
