"""Prepare disclosed baseline Authentication-facade seals; never invoke Lean.

The facade has no stored constants. Its source/import graph are exact base Git
bytes. Request metadata is reconstructed from the genuine earlier base census
for its covered modules, plus a current census of only unchanged additional
base modules. The resulting seal imports current compiled owned modules; that
limitation is explicit and is not presented as a pure baseline proof run.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
EVIDENCE = HERE.parents[1]
BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
FACADE = 'TCSlib.Cryptography.Authentication'
OWNED = 'TCSlib.Cryptography.Authentication.Signatures.HashAndSign'
sys.dont_write_bytecode = True
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('action', choices=['collect', 'seals'])
parser.add_argument('--repo', type=Path, default=Path('/private/tmp/hash-sign-fill/repo'))
parser.add_argument('--out', type=Path, default=EVIDENCE / 'rule10/base-facade')
parser.add_argument('--old-base-log', type=Path, default=EVIDENCE / 'logs/rule10-base-collect-1.log')
parser.add_argument('--current-census-log', type=Path)
args = parser.parse_args()
repo, out = args.repo.resolve(), args.out.resolve()
out.mkdir(parents=True, exist_ok=True)
sub = '.lake/hash-sign-rule10/base-facade'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(*commands):
    return subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), *commands])


def dump(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    raw = (json.dumps(value, indent=2, ensure_ascii=False) + '\n').encode()
    if path.exists() and path.read_bytes() != raw:
        raise RuntimeError('refusing to overwrite different preparation: ' + str(path))
    path.write_bytes(raw)


spec = importlib.util.spec_from_file_location('hash_sign_facade_base_builder', HERE / 'archived-gate10-tools/build_seals.py')
bs = importlib.util.module_from_spec(spec)
spec.loader.exec_module(bs)
facade_raw = git('show', BASE + ':' + FACADE.replace('.', '/') + '.lean')
facade_header = bs.header(facade_raw)
if any(not (bs.IMPORT_RE.fullmatch(line.strip()) or line.strip().startswith('set_option '))
       for line in facade_header['code'].splitlines() if line.strip()):
    raise RuntimeError('baseline facade has commands beyond imports/options; cannot claim zero stored constants')
graph, hashes = {}, {}
stack = [m for m in facade_header['imports'] if m.startswith('TCSlib.') or m == 'TCSlib']
while stack:
    module = stack.pop()
    if module in graph:
        continue
    raw = git('show', BASE + ':' + module.replace('.', '/') + '.lean')
    graph[module] = [m for m in bs.header(raw)['imports'] if m.startswith('TCSlib.') or m == 'TCSlib']
    hashes[module] = sha(raw)
    stack += graph[module]
closure = sorted(graph)
dump(out / 'base-import-graph.json', {'base': BASE, 'facade': FACADE, 'source_sha256': sha(facade_raw),
     'direct_imports': facade_header['imports'], 'closure': closure, 'graph': graph, 'module_source_sha256': hashes,
     'stored_constants': 0, 'zero_constants_basis': 'Exact base source has only import/set_option commands.'})
versions = out / 'tool-versions'
versions.mkdir(exist_ok=True)
for path in [Path(__file__), HERE / 'mkseals_ab.py', HERE / 'NmCollect.template.lean', HERE / 'run_probe.py',
             EVIDENCE / 'tools/check_module.py', *(HERE / 'archived-gate10-tools').glob('*.py')]:
    raw = path.read_bytes()
    (versions / (path.stem + '-' + sha(raw) + path.suffix)).write_bytes(raw)

if args.action == 'collect':
    import re
    source = (HERE / 'NmCollect.template.lean').read_text()
    start = source.index('def owners : List Name := [')
    end = source.index(']', start)
    source = source[:start] + 'def owners : List Name := [' + source[end:]
    source = re.sub(r'^import TCSlib\S*\n', '', source, flags=re.M)
    source = source.replace('import Lean\n', 'import Lean\n' + ''.join('import ' + m + '\n' for m in facade_header['imports']), 1)
    source += '\n-- This census loads current compiled dependencies; baseline requests are reconstructed separately.\n'
    source += 'run_cmd do\n  IO.println ' + json.dumps('CURRENT-ARTIFACT-CENSUS FOR BASE-IMPORT-ONLY-FACADE; NOT A PURE BASELINE RUN') + '\n'
    probe = repo / (sub + '/CurrentCatalog.lean')
    probe.parent.mkdir(parents=True, exist_ok=True)
    if probe.exists():
        raise RuntimeError('catalog probe already prepared')
    probe.write_text(source)
    (out / 'CurrentCatalog.lean').write_text(source)
    (out / 'base-Authentication.lean').write_bytes(facade_raw)
    print('census_module:', sub + '/CurrentCatalog')
else:
    if args.current_census_log is None:
        raise RuntimeError('--current-census-log required after a successful separately checked census')
    old_text, current_text = args.old_base_log.read_text(), args.current_census_log.read_text()
    if not old_text.rstrip().endswith('exit: 0') or not current_text.rstrip().endswith('exit: 0'):
        raise RuntimeError('census inputs must be completed successful checks')
    def parse(text):
        return {r['name']['display']: r for line in text.splitlines() if line.startswith('CAT ')
                for r in [json.loads(line[4:])]}
    old, current = parse(old_text), parse(current_text)
    old_closures = [json.loads(line[8:]) for line in old_text.splitlines() if line.startswith('CLOSURE ')]
    old_coverage = set(next(r['closure'] for r in old_closures if r['module'] == OWNED)) | {OWNED}
    reused = {name: row for name, row in old.items() if row['home']['display'] in set(closure) & old_coverage}
    additions = {name: row for name, row in current.items() if row['home']['display'] in set(closure) - old_coverage}
    verified_unchanged = []
    for module in sorted(set(closure) - old_coverage):
        path = module.replace('.', '/') + '.lean'
        if sha((repo / path).read_bytes()) != hashes[module]:
            raise RuntimeError('additional module differs from base source: ' + module)
        verified_unchanged.append(module)
    for name, row in reused.items():
        if current.get(name) != row:
            raise RuntimeError('base candidate identity/status differs in current loaded catalog: ' + name)
    catalog = dict(reused)
    if set(catalog) & set(additions):
        raise RuntimeError('duplicate reconstructed native name')
    catalog.update(additions)
    reconstructed = out / 'reconstructed-base-facade-catalog.log'
    with reconstructed.open('w') as f:
        print('DISCLOSURE: exact base facade source/import graph; genuine old baseline metadata reused for covered modules; current-loaded unchanged extra modules verified source-identical; seal imports current owned artifacts, not a pure baseline proof tree.', file=f)
        print('CLOSURE ' + json.dumps({'module': FACADE, 'closure': closure}), file=f)
        for name in sorted(catalog):
            print('CAT ' + json.dumps(catalog[name], ensure_ascii=False), file=f)
        print('CAT-COUNT ' + str(len(catalog)), file=f)
        print('MODULE ' + FACADE + ': stored 0', file=f)
    dump(out / 'catalog-reconstruction.json', {'base': BASE, 'facade': FACADE, 'stored_constants': 0,
         'base_source_sha256': sha(facade_raw), 'old_base_log': str(args.old_base_log),
         'old_base_log_sha256': sha(args.old_base_log.read_bytes()), 'current_census_log': str(args.current_census_log),
         'current_census_log_sha256': sha(args.current_census_log.read_bytes()), 'old_coverage_modules': sorted(old_coverage),
         'reused_base_definitions': len(reused), 'additional_current_definitions': len(additions),
         'additional_modules_verified_source_equal_base': verified_unchanged,
         'all_reused_native_metadata_equal_current': True, 'closure_modules': len(closure),
         'limitation': 'Baseline facade source and requests are reconstructed, but checks load current compiled owned dependencies. No changed proof is claimed to be checked at base.'})
    for letter in ['A', 'B']:
        env = dict(os.environ, SEAL_CHUNK='500')
        if letter == 'B': env['SEAL_EVAL'] = '1'
        else: env.pop('SEAL_EVAL', None)
        subprocess.run([sys.executable, '-I', str(HERE / 'mkseals_ab.py'), str(HERE / 'archived-gate10-tools'),
              str(reconstructed), str(repo), BASE, str(out / ('seal-' + letter)), sub, 'Seal' + letter + '_', FACADE],
              check=True, env=env)
