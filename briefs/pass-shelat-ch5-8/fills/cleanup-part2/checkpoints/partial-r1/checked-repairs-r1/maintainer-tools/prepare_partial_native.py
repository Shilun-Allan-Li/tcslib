"""Prepare an exact current-source closure for bounded maintainer repairs."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PREP = Path(__file__).resolve().parent
WORK = Path('/Users/seyoonr/.codex/worktrees/ps-gate08-repair/tcslib-pass-shelat-ch2-4')
OUT = PREP / 'partial-r1/native-fixes-r1'
TARGETS = [
    'TCSlib/Complexity/Randomized/PPT',
    'TCSlib/Cryptography/Asymptotic/HardCoreLemmas',
    'TCSlib/Cryptography/Asymptotic/HardCoreCollection',
    'TCSlib/Cryptography/Asymptotic/HardCore',
    'TCSlib/Cryptography/ZeroKnowledge/EncodingMachines',
    'TCSlib/Cryptography/Asymptotic/OneWayLemmas',
    'TCSlib/Cryptography/Asymptotic/GGMReduction',
    'TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep',
]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def mask_comments(raw):
    # Header imports precede all real commands; strings only occur inside the
    # leading comments here. Keep newlines and nested comment boundaries exact.
    chars = list(raw)
    depth = 0
    i = 0
    while i < len(raw):
        if raw.startswith('/-', i):
            depth += 1
            chars[i:i+2] = '  '
            i += 2
        elif depth and raw.startswith('-/', i):
            depth -= 1
            chars[i:i+2] = '  '
            i += 2
        elif not depth and raw.startswith('--', i):
            end = raw.find('\n', i)
            if end < 0:
                end = len(raw)
            chars[i:end] = ' ' * (end-i)
            i = end
        else:
            if depth and raw[i] != '\n':
                chars[i] = ' '
            i += 1
    assert depth == 0
    return ''.join(chars)


def imports(raw):
    result = []
    for line in mask_comments(raw).splitlines():
        line = line.strip()
        if not line or line in ['prelude', 'module']:
            continue
        if not line.startswith('import '):
            break
        tokens = line[len('import '):].split()
        assert tokens and all(re.fullmatch(r'[A-Za-z_][A-Za-z_0-9.]*', name) for name in tokens), line
        result.extend(tokens)
    return result


def main():
    branch = subprocess.check_output(['git', '-C', str(WORK), 'branch', '--show-current'], text=True).strip()
    head = subprocess.check_output(['git', '-C', str(WORK), 'rev-parse', 'HEAD'], text=True).strip()
    assert branch == 'cryptography/pass-shelat-cleanup-part2-final-review'
    assert head == 'bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3'
    assert not OUT.exists(), 'A phase plan is immutable; choose a new phase for new source'
    rows = []
    states = {}
    external = set()
    def visit(module):
        if states.get(module) == 'done':
            return
        assert module not in states, ('Local import cycle', module)
        states[module] = 'visiting'
        path = WORK / (module + '.lean')
        raw = path.read_bytes()
        deps = imports(raw.decode())
        local = [name.replace('.', '/') for name in deps if name.startswith('TCSlib.')]
        foreign = [name for name in deps if not name.startswith('TCSlib.')]
        for dep in local:
            visit(dep)
        external.update(foreign)
        rows.append({'module': module, 'source_sha256': sha(raw),
                     'local_imports': local, 'external_imports': foreign})
        states[module] = 'done'
    for target in TARGETS:
        visit(target)
    OUT.mkdir()
    (OUT / 'modules.json').write_text(json.dumps(rows, indent=2) + '\n')
    (OUT / 'order.txt').write_text(''.join(row['module'] + '\n' for row in rows))
    roots = sorted(name for name in external if name.startswith('Mathlib.'))
    (OUT / 'mathlib-roots.txt').write_text('\n'.join(roots) + '\n')
    # Check all direct external products before starting a native/cache probe.
    package_dirs = sorted(path for path in (WORK / '.lake/packages').iterdir() if path.is_dir())
    missing = []
    for name in sorted(external):
        rel = Path(name.replace('.', '/') + '.olean')
        candidates = [path / '.lake/build/lib/lean' / rel for path in package_dirs]
        candidates.append(Path.home() / '.elan/toolchains/leanprover--lean4---v4.25.0/lib/lean' / rel)
        if not any(path.is_file() and path.stat().st_size for path in candidates):
            missing.append(name)
    config = {
        'kind': 'COLD_LOCAL_REPAIR_CLOSURE_NOT_FULL_CLEANUP_ACCEPTANCE',
        'branch': branch, 'head_before_repairs_committed': head,
        'worktree': str(WORK), 'output': str(OUT),
        'tree': str(WORK / '.lake/ps-maintainer/cleanup-partial-fixes-20261108-r1/oleans'),
        'targets': TARGETS, 'module_count': len(rows),
        'mathlib_roots': len(roots), 'direct_external_modules': len(external),
        'missing_direct_external_objects': missing,
        'modules_sha256': sha((OUT / 'modules.json').read_bytes()),
        'order_sha256': sha((OUT / 'order.txt').read_bytes()),
        'working_source_diff_sha256': sha(subprocess.check_output(['git', '-C', str(WORK), 'diff', '--binary'])),
        'checker_sha256': sha((WORK / 'scripts/lean_check_tree.sh').read_bytes()),
        'limits': 'Selected current-source repair targets plus their complete local import closure. Fresh TCSlib objects, ordinary PATH, existing pinned package cache; not the full affected/root/Checks or seal replay.',
    }
    (OUT / 'config.json').write_text(json.dumps(config, indent=2) + '\n')
    assert not missing, ('Fetch only the missing direct roots before native checking', missing)
    print(json.dumps({key: value for key, value in config.items() if key not in ['limits', 'targets']}, indent=2))


if __name__ == '__main__':
    main()
