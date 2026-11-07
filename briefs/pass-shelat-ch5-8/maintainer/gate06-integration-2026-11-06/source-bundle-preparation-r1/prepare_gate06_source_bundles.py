"""Prepare immutable source-only audit bundles; does not issue or stage a gate."""
from pathlib import Path
import hashlib, importlib.util, json, subprocess, sys
sys.dont_write_bytecode = True
ROOT = Path.cwd()
G06 = ROOT / '.lake/ps-maintainer/gate06'
E = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-final-r1')
OUT = G06 / 'repairs/source-bundles-final-r1'
HEAD = '3f6db40e1688c4a0bb922c9575dd3bd2157a650b'
BUILDER_SHA = 'fae07000e8c3fda22225632ded45208e2651bab827d827639f48d46e2005347a'
BUNDLER_SHA = 'c5bc65a54d1cbd4974690330970d15af80ffa55a06a84885c44b75bd36bb8ec9'
sha = lambda raw: hashlib.sha256(raw).hexdigest()

def need(ok, message):
    if not ok:
        raise RuntimeError(message)

def load_builder():
    path = G06 / 'build_seals.py'
    need(sha(path.read_bytes()) == BUILDER_SHA, 'builder changed')
    spec = importlib.util.spec_from_file_location('source_bundle_header', path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod

def main():
    bs = load_builder()
    pins = json.loads((E / 'pins.json').read_text())
    need(pins['head'] == HEAD, 'source pin changed')
    library, snapshot = bs.library_snapshot(ROOT, pins)
    bundler = ROOT / 'briefs/pass-shelat-ch5-8/maintainer/tools/mkbundle2.py'
    need(sha(bundler.read_bytes()) == BUNDLER_SHA, 'bundler changed')
    need(not OUT.exists(), 'do not overwrite source bundles')
    need(subprocess.run(['git','check-ignore','-q',str(OUT)], cwd=ROOT).returncode == 0, 'output must be ignored')
    roots = {
        '06A': ['TCSlib.Cryptography.Authentication'],
        '06B': ['TCSlib.Cryptography.SecureComputation'],
        '06C': ['TCSlib.Cryptography.Composability'],
        '06D': ['TCSlib.Cryptography.Randomness', 'TCSlib.LearningTheory.PAC.Defs',
                'TCSlib.LearningTheory.PAC.Prediction', 'TCSlib.InformationTheory.Samples'],
    }
    OUT.mkdir()
    result = {'status':'SOURCE_ONLY_UNISSUED_UNSTAGED', 'head':HEAD, 'snapshot':snapshot,
              'builder_sha256':BUILDER_SHA, 'bundler_sha256':BUNDLER_SHA,
              'root_export_context_is_not_import_closure_root': True, 'packs':{}}
    for pack, primary in roots.items():
        found, visiting, edges = set(), set(), {}
        def visit(module):
            need(module not in visiting, 'cyclic import: ' + module)
            if module in found:
                return
            path = module.replace('.', '/') + '.lean'
            need(path in library, 'missing module: ' + module)
            visiting.add(module)
            deps = [m for m in bs.header(library[path])['imports'] if m == 'TCSlib' or m.startswith('TCSlib.')]
            edges[module] = deps
            for dep in deps:
                visit(dep)
            visiting.remove(module)
            found.add(module)
        for module in primary:
            visit(module)
        paths = sorted({m.replace('.', '/') + '.lean' for m in found} | {'TCSlib.lean'})
        filelist = OUT / (pack + '-SOURCE-FILES.txt')
        filelist.write_text(''.join(HEAD + ' ' + p + '\n' for p in paths))
        bundle = OUT / (pack + '-source-only.md')
        proc = subprocess.run([sys.executable, '-I', str(bundler), str(ROOT), str(bundle), str(filelist)], capture_output=True, text=True)
        (OUT / (pack + '-bundler.log')).write_text(proc.stdout + proc.stderr)
        need(proc.returncode == 0, 'source bundler failed: ' + pack)
        result['packs'][pack] = {'primary_modules':primary, 'closure_module_count':len(found),
            'module_import_edges':edges, 'included_path_count':len(paths),
            'files':[{'revision':HEAD,'path':p,'bytes':len(library[p]),'sha256':sha(library[p])} for p in paths],
            'bundle_path':str(bundle.relative_to(ROOT)), 'bundle_bytes':bundle.stat().st_size,
            'bundle_sha256':sha(bundle.read_bytes()), 'filelist_sha256':sha(filelist.read_bytes())}
    (OUT / 'manifest.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({p:{k:v for k,v in d.items() if k in ['closure_module_count','included_path_count','bundle_bytes','bundle_sha256']} for p,d in result['packs'].items()},indent=2))

if __name__ == '__main__':
    main()
