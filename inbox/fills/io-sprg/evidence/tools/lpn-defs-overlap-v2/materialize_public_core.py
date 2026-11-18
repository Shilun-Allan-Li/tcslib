"""Root-only materialization of ONE public composition probe; NEVER invokes Lean.
Safely handles := and __PROBE_BODY__ on separate lines, preserves the original
global no-owned-import guard, and requires exactly one full anonymous example.
"""
from pathlib import Path
import argparse, hashlib, json, re
WORKTREE = Path('/Users/seyoonr/.codex/worktrees/io-sprg/tcslib-exchange')
PACKET = Path('/private/tmp/io-sprg-proof-notes/M4LPNPrepared')
EXPECTED_PUBLIC_INDEX_SHA256 = '6671da552cca51c171eb804001fe93297e68979764b82f31a72313e5f176ecc3'

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def materialize(text, mode):
    if text.count('__PROBE_BODY__') != 1:
        raise RuntimeError('Require one proof marker')
    if len(re.findall(r'^example\b', text, re.M)) != 1:
        raise RuntimeError('Require exactly one full anonymous example')
    imports = [line[7:] for line in text.splitlines() if line.startswith('import ')]
    if imports != ['TCSlib.Cryptography.Games.Bridges.Experiments',
                   'Lean.Elab.Tactic.LibrarySearch']:
        raise RuntimeError('Public core imports differ from their reviewed public roots')
    if any(line.startswith('import TCSlib.Cryptography.Obfuscation')
           for line in text.splitlines()):
        raise RuntimeError('Owned imports are forbidden in these public-only cores')
    result, count = re.subn(r'\s*:=\s*__PROBE_BODY__',
                           '\n  := by\n    ' + mode + '?', text)
    if count != 1 or len(re.findall(r':=\s*by\b', result)) != 1:
        raise RuntimeError('Require one normalized proof assignment')
    if '__PROBE_BODY__' in result or len(re.findall(r'^example\b', result, re.M)) != 1:
        raise RuntimeError('The exact full example was not retained')
    if max(map(len, result.splitlines())) > 100:
        raise RuntimeError('Generated Lean line exceeds100 characters')
    return result

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('core', type=int, choices=(1, 2, 3))
    ap.add_argument('mode', choices=('exact', 'apply'))
    ap.add_argument('--tag', required=True)
    ap.add_argument('--packet', type=Path, default=PACKET)
    a = ap.parse_args()
    if not re.fullmatch(r'[A-Za-z0-9_]+', a.tag):
        raise RuntimeError('Use a fresh safe immutable tag')
    packet = a.packet.resolve()
    index_path = packet / 'overlap/public-core-index.json'
    if sha(index_path) != EXPECTED_PUBLIC_INDEX_SHA256:
        raise RuntimeError('Reviewed public-core index changed')
    row = json.loads(index_path.read_text())[a.core - 1]
    template = packet / 'overlap/public-cores' / Path(row['template']).name
    if sha(template) != row['sha256']:
        raise RuntimeError('Reviewed public-core template changed')
    text = materialize(template.read_text(), a.mode)
    stem = template.name.removesuffix('.lean.template')
    name = 'M4LPNPublic_' + a.tag + '_' + stem
    module = Path('/private/tmp/io-sprg-overlap') / (name + '-' + a.mode)
    source = module.with_suffix('.lean')
    order = WORKTREE / 'evidence/logs' / ('overlap-' + name + '-' + a.mode + '.txt')
    manifest_dir = packet / 'root-review/public-materialized' / name / a.mode
    if source.exists() or order.exists() or manifest_dir.exists():
        raise RuntimeError('Preserve old probes; use a fresh tag')
    global_tool = WORKTREE / 'evidence/tools/overlap_step.py'
    ban = "assert not any(l.startswith('import TCSlib.Cryptography.Obfuscation') for l in s.splitlines())"
    if ban not in global_tool.read_text():
        raise RuntimeError('Global no-owned-import guard is not intact')
    source.parent.mkdir(parents=True, exist_ok=True)
    source.write_text(text)
    order.parent.mkdir(parents=True, exist_ok=True)
    with order.open('x') as f:
        f.write(str(module) + '\n')
    manifest_dir.mkdir(parents=True, exist_ok=False)
    command = ['python3', '-I', str(WORKTREE / 'evidence/tools/seal/runner_full.py'),
               str(WORKTREE), str(order), str(WORKTREE / '.lake/io-sprg-oleans'),
               str(WORKTREE / 'evidence/overlap/runs')]
    (manifest_dir / 'manifest.json').write_text(json.dumps({
        'status': 'PREPARED_NOT_RUN', 'scope': 'PUBLIC_COMPONENT_NOT_ORIGINAL_FULL_STATEMENT',
        'source': str(source), 'source_sha256': sha(source),
        'template': str(template), 'template_sha256': sha(template),
        'global_overlap_guard_sha256': sha(global_tool), 'one_full_example': True,
        'proof_blocks': 1, 'runner_command_for_root_only': command,
        'qualification': 'No StructuredSeed import; source only materialized. This script '
            'does not invoke Lean. Original ten exact statements use the separate Defs driver.'},
        indent=2) + '\n')
    print('PUBLIC_CORE_PREPARED_NOT_RUN', source)
    print(json.dumps(command))

if __name__ == '__main__':
    main()
