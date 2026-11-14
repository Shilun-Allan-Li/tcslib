"""Prepare hash-sign Rule-10 evidence; this tool never starts Lean or Lake.

The archived collector and native-name seal instrumenter are retained verbatim.
This adapter supplies precise owner imports, all-constant axioms, paired
controls, and phase-specific paths. Run all probes separately with the required
scripts/lean_check_tree.sh command. See README.md beside this file.
"""
import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
OWNED = 'TCSlib.Cryptography.Authentication.Signatures.HashAndSign'
AUTH_FACADE = 'TCSlib.Cryptography.Authentication'


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def write(path, raw):
    path.parent.mkdir(parents=True, exist_ok=True)
    if isinstance(raw, str):
        raw = raw.encode()
    if path.exists():
        if path.read_bytes() != raw:
            raise RuntimeError('refusing to overwrite different preparation: ' + str(path))
    else:
        path.write_bytes(raw)


def dump(path, obj):
    write(path, json.dumps(obj, indent=2, ensure_ascii=False) + '\n')


def command(args, cwd=None):
    return subprocess.check_output(args, cwd=cwd, text=True)


def git(repo, *args):
    return command(['git', '--no-optional-locks', '-C', str(repo), *args]).strip()


def owners_at(repo, rev):
    facade = OWNED.replace('.', '/') + '.lean'
    helper_dir = OWNED.replace('.', '/')
    paths = git(repo, 'ls-tree', '-r', '--name-only', rev, '--', facade, helper_dir,
                AUTH_FACADE.replace('.', '/') + '.lean').splitlines()
    paths = sorted(p for p in paths if p.endswith('.lean'))
    owners = [p[:-5].replace('/', '.') for p in paths]
    current = [p.relative_to(repo).as_posix() for p in (repo / helper_dir).rglob('*.lean')]
    absent = [p[:-5].replace('/', '.') for p in sorted(set(current) - set(paths))]
    if OWNED not in owners:
        raise RuntimeError('owned module absent at revision')
    return owners, absent


def capture_probe(repo, rel, out, raw):
    write(repo / (rel + '.lean'), raw)
    write(out / 'sources' / (Path(rel).name + '.lean'), raw)
    return {'module': rel, 'source_sha256': sha(raw.encode() if isinstance(raw, str) else raw)}


def collect(args, repo, rev, out, sub, owners, absent):
    template = (HERE / 'NmCollect.template.lean').read_text()
    start = template.index('def owners : List Name := [')
    end = template.index(']', start)
    source = template[:start] + 'def owners : List Name := [\n  ' + ',\n  '.join('`' + m for m in owners) + template[end:]
    import re
    source = re.sub(r'^import TCSlib\S*\n', '', source, flags=re.M)
    source = source.replace('import Lean\n', 'import Lean\n' + ''.join('import ' + m + '\n' for m in owners), 1)
    source += '''

-- Hash-sign adapter: all stored constants, including private/generated ones.
run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let mut count := 0
  for (c, _) in env.constants.toList do
    let some mi := env.getModuleIdxFor? c | continue
    let home := names[mi.toNat]!
    unless owners.contains home do continue
    let axs ← liftCoreM (Lean.collectAxioms c)
    let axs := (axs.map (·.toString)).qsort (· < ·)
    IO.println s!"AXIOMS {home} | {c} | {axs.toList}"
    count := count + 1
  IO.println s!"AXIOMS-STORED-COUNT {count}"

#print axioms TCSlib.Cryptography.Authentication.hashAndSign_oneTimeSecure
'''
    probe = capture_probe(repo, sub + '/Collect', out, source)
    dump(out / 'collect-plan.json', {'phase': args.phase, 'rev': rev, 'owners': owners,
         'absent_at_revision': absent, 'probe': probe,
         'collector_template_sha256': sha((HERE / 'NmCollect.template.lean').read_bytes()),
         'adapter_sha256': sha(Path(__file__).read_bytes()),
         'scope': 'Every stored constant, including private/generated; complete TCSlib import closures.'})
    write(out / 'owners.txt', '\n'.join(owners) + '\n')
    print(json.dumps(probe))


def seals(args, repo, rev, out, sub, owners, absent):
    if not args.collector_log:
        raise RuntimeError('--collector-log is required')
    log = Path(args.collector_log).resolve()
    for letter in ['A', 'B']:
        dest = out / ('seal-' + letter)
        if (dest / 'manifest.json').exists():
            raise RuntimeError('seal preparation already exists: ' + str(dest))
        env = dict(os.environ, SEAL_CHUNK=str(args.seal_chunk))
        if letter == 'B':
            env['SEAL_EVAL'] = '1'
        else:
            env.pop('SEAL_EVAL', None)
        subprocess.run([sys.executable, '-I', str(HERE / 'mkseals_ab.py'),
             str(HERE / 'archived-gate10-tools'), str(log), str(repo), rev,
             str(dest), sub, 'Seal' + letter + '_', *owners], check=True, env=env)
    print('Seal sources/requests prepared; run each manifest probe through lean_check_tree.sh.')


def load_builder(chunk=500):
    def load(path, name):
        spec = importlib.util.spec_from_file_location(name, path)
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        return module
    tools = HERE / 'archived-gate10-tools'
    bs = load(tools / 'build_seals.py', 'hash_sign_seals')
    ctl = load(tools / 'build_controls.py', 'hash_sign_controls')
    adapter = load(tools / 'request_payload_adapter.py', 'hash_sign_adapter')
    adapter.configure_builders(bs, ctl)
    original = bs.seal_command
    def chunked(label, rows, *, end):
        return b''.join(original(label + '_part' + str(i // chunk + 1), rows[i:i + chunk], end=end)
                        for i in range(0, len(rows), chunk)) if rows else original(label, rows, end=end)
    bs.seal_command = chunked
    return bs


CONTROL_BODIES = {
 'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy': ('costBoundedBy',
  'theorem negative {ι α : Type} {spec : TCSlib.Cryptography.Games.OracleSpec ι} (a : α) (q : ℕ) : (TCSlib.Cryptography.Games.OracleComp.pure (spec := spec) a).CostBoundedBy (fun _ => 1) q := True.intro\n',
  'theorem positive {ι α : Type} {spec : TCSlib.Cryptography.Games.OracleSpec ι} (a : α) (q : ℕ) : (TCSlib.Cryptography.Games.OracleComp.pure (spec := spec) a).CostBoundedBy (fun _ => 1) q := TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure (fun _ => 1) a q\n'),
 'Complexity.PolyExpr.eval': ('eval',
  'theorem negative (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl\n',
  'theorem positive (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := Complexity.PolyExpr.eval_const 2 n\n'),
 'TCSlib.Cryptography.padFin': ('padFin',
  'theorem negative (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := rfl\n',
  'theorem positive (l : ℕ) (w : List Bool) (i : Fin l) : TCSlib.Cryptography.padFin l w i = w.getD i false := TCSlib.Cryptography.padFin_apply l w i\n'),
 'Complexity.NUPPT.inArg': ('inArg',
  'theorem negative (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := rfl\n',
  'theorem positive (z : List Bool) : Complexity.NUPPT.inArg z = Complexity.pairSndD (Complexity.pairFstD (Complexity.pairFstD z)) := Complexity.NUPPT.inArg_eq z\n'),
 'TCSlib.Cryptography.Authentication.HashSignFill.collisionKey': ('collisionKey',
  'theorem negative (S : TCSlib.Cryptography.Authentication.SignatureScheme) (c : List Bool) : TCSlib.Cryptography.Authentication.HashSignFill.collisionKey S c = S.gen.output (Complexity.NUPPT.layout (Complexity.pairFstD c) [] [] ((Complexity.pairSndD (Complexity.pairSndD c)).take (S.gen.coins.eval (Complexity.pairFstD c).length))) := rfl\n',
  'theorem positive (S : TCSlib.Cryptography.Authentication.SignatureScheme) (c : List Bool) : TCSlib.Cryptography.Authentication.HashSignFill.collisionKey S c = S.gen.output (Complexity.NUPPT.layout (Complexity.pairFstD c) [] [] ((Complexity.pairSndD (Complexity.pairSndD c)).take (S.gen.coins.eval (Complexity.pairFstD c).length))) := TCSlib.Cryptography.Authentication.HashSignFill.collisionKey_eq S c\n'),
 'TCSlib.Cryptography.Authentication.HashSignForward.indexWord': ('indexWord',
  'theorem negative (H : TCSlib.Cryptography.Authentication.CRH) (u ω : List Bool) : TCSlib.Cryptography.Authentication.HashSignForward.indexWord H u ω = H.gen.output (Complexity.NUPPT.layout u [] [] ω) := rfl\n',
  'theorem positive (H : TCSlib.Cryptography.Authentication.CRH) (u ω : List Bool) : TCSlib.Cryptography.Authentication.HashSignForward.indexWord H u ω = H.gen.output (Complexity.NUPPT.layout u [] [] ω) := TCSlib.Cryptography.Authentication.HashSignForward.indexWord_eq H u ω\n'),
}


def controls(args, repo, rev, out, sub, owners, absent):
    bs = load_builder(args.seal_chunk)
    plan = []
    for letter in ['A', 'B']:
        records = [json.loads(p.read_text()) for p in sorted((out / ('seal-' + letter)).glob('Seal' + letter + '_*.json'))]
        if not records:
            raise RuntimeError('prepare seals first')
        for target, (tag, negative, positive) in CONTROL_BODIES.items():
            candidates = [r for r in records if target in {x['spelling'] for x in r['rows']}]
            if not candidates:
                plan.append({'target': target, 'variant': letter, 'absent_from_request_sets': True})
                continue
            record = min(candidates, key=lambda r: (len(r['rows']), r['label']))
            requests = record['rows'] if args.control_mode == 'whole' else [r for r in record['rows'] if r['spelling'] == target]
            original = subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), 'show',
                       record['rev'] + ':' + record['source']])
            direct_imports = bs.header(original)['imports']
            imports = list(dict.fromkeys(['Lean', *direct_imports]))
            for sealed in [False, True]:
                label = ('ControlForeign' if args.control_mode == 'whole' else 'ControlSingleton') + letter + ('S_' if sealed else 'U_') + tag
                src = (''.join('import ' + module + '\n' for module in imports) + '\nset_option maxHeartbeats 0\n'
                       'set_option autoImplicit false\nset_option relaxedAutoImplicit false\n\n').encode()
                if sealed:
                    src += bs.seal_command(label, requests, end=False)
                src += b'namespace HashSignSensitivity\n\n'
                negative_start = src.count(b'\n') + 1
                src += negative.encode() + b'\n'
                positive_start = src.count(b'\n') + 1
                src += positive.encode() + b'\nend HashSignSensitivity\n\n'
                if sealed:
                    src += bs.seal_command(label, requests, end=True)
                probe = capture_probe(repo, sub + '/' + label, out, src)
                plan.append(dict(probe, target=target, variant=letter, sealed=sealed,
                     owner=record['module'], request_record=record['label'], requested=len(requests) if sealed else 0,
                     request_mode=args.control_mode, request_names=[r['spelling'] for r in requests],
                     direct_imports=imports, imports_owner=False,
                     negative_start_line=negative_start, positive_start_line=positive_start,
                     expected_error_count=1 if sealed else 0,
                     expected_error_declaration='HashSignSensitivity.negative' if sealed else None))
    dump(out / 'controls-plan.json', plan)
    print('Controls prepared:', sum('module' in p for p in plan), '; sealed negatives must each fail exactly once.')


def scan(args, repo, rev, out, sub, owners, absent):
    files = [m.replace('.', '/') + '.lean' for m in owners]
    touched = out / 'touched.json'
    log = command([sys.executable, '-I', str(HERE / 'touched.py'), str(repo), args.base, rev, str(touched), *files])
    write(out / 'touched.log', log)
    probe = repo / (sub + '/ExplicitKinds.lean')
    probe.parent.mkdir(parents=True, exist_ok=True)
    if probe.exists():
        raise RuntimeError('scan preparation already exists')
    items = out / 'explicit-items.json'
    log = command([sys.executable, '-I', str(HERE / 'scan1.py'), str(HERE / 'archived-gate10-tools/scan_explicit.py'),
                  str(repo), str(touched), str(items), str(probe), *files])
    write(out / 'explicit-prepare.log', log)
    raw = probe.read_bytes()
    write(out / 'sources/ExplicitKinds.lean', raw)
    dump(out / 'explicit-plan.json', {'probe': {'module': sub + '/ExplicitKinds', 'source_sha256': sha(raw)},
          'items': str(items), 'phase2_command': [sys.executable, '-I', str(HERE / 'scan2.py'),
          str(items), 'NATIVE_KINDS_LOG', str(out / 'explicit-final.json')]})
    print('Native kinds probe:', sub + '/ExplicitKinds')


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('action', choices=['collect', 'seals', 'controls', 'scan'])
    p.add_argument('--repo', required=True, type=Path)
    p.add_argument('--phase', required=True, choices=['base', 'final'])
    p.add_argument('--rev', default='HEAD')
    p.add_argument('--base', default=BASE)
    p.add_argument('--out', required=True, type=Path)
    p.add_argument('--collector-log')
    p.add_argument('--control-mode', choices=['whole', 'singleton'], default='singleton')
    p.add_argument('--seal-chunk', type=int, default=500)
    args = p.parse_args()
    if args.seal_chunk <= 0:
        p.error('--seal-chunk must be positive')
    repo, out = args.repo.resolve(), args.out.resolve()
    rev = git(repo, 'rev-parse', args.rev + '^{commit}')
    owners, absent = owners_at(repo, rev)
    if args.phase == 'final' and absent:
        raise RuntimeError('final revision omits working helper source(s): ' + ', '.join(absent))
    if args.phase == 'final':
        for module in owners:
            path = module.replace('.', '/') + '.lean'
            committed = subprocess.check_output(['git', '--no-optional-locks', '-C', str(repo), 'show', rev + ':' + path])
            if (repo / path).read_bytes() != committed:
                raise RuntimeError('final working source differs from selected revision: ' + path)
    sub = '.lake/hash-sign-rule10/' + args.phase
    out.mkdir(parents=True, exist_ok=True)
    adapter_raw = Path(__file__).read_bytes()
    write(out / 'tool-versions' / ('prepare-' + sha(adapter_raw) + '.py'), adapter_raw)
    if args.action in ['seals', 'controls']:
        dump(out / (args.action + '-batching.json'), {'maximum_requests_per_command': args.seal_chunk,
             'coverage_changed': False, 'native_name_guards_changed': False, 'instance_mask_guards_changed': False,
             'eof_verification_changed': False})
    globals()[args.action](args, repo, rev, out, sub, owners, absent)


if __name__ == '__main__':
    main()
