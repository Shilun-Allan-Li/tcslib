#!/usr/bin/env python3
"""Axioms of every stored constant of the given modules, and of the campaign endpoints named in
the brief (`ENDPOINT` lines). Writes scratch/ax/<TAG>.lean (imports: the modules and the endpoint
modules), runs it with the olean tree, writes the log.
usage: axioms.py TAG LOG MODULE..."""
import os, subprocess, sys
tag, log, mods = sys.argv[1], sys.argv[2], sys.argv[3:]
R = '/workspace/plong'
EP_MODS = ['TCSlib/Cryptography/Encryption/PrivateKey/FromPRF',
           'TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF',
           'TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag',
           'TCSlib/Cryptography/Pseudorandom/Functions/Asymptotic/GGM']
EP = ['TCSlib.Cryptography.prfScheme_multiMessageSecure',
      'TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg',
      'TCSlib.Cryptography.Composability.prfFixedScheme_cpa',
      'TCSlib.Cryptography.Composability.ccaScheme_cca2',
      'TCSlib.Cryptography.exists_prf_of_exists_prg']
os.makedirs(f'{R}/scratch/ax', exist_ok=True)
names = ', '.join('`' + m.replace('/', '.') for m in mods)
imps = list(dict.fromkeys(mods + EP_MODS))
src = '\n'.join('import ' + m.replace('/', '.') for m in imps) + f'''

open Lean Elab Command

/-! prf-long fill, axioms ({tag}): every stored constant of the listed modules (`AX` lines) and the
consumer endpoints of the brief (`ENDPOINT` lines). -/

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods : Std.HashSet Name := Std.HashSet.ofList [{names}]
  let mut out : Array String := #[]
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless mods.contains mod do continue
    let axs ← liftCoreM <| collectAxioms c
    let axs := (axs.map toString).qsort (· < ·)
    out := out.push s!"AX\\t{{mod}}\\t{{c}}\\t{{axs.toList}}"
  for s in out.qsort (· < ·) do IO.println s
  IO.println s!"TOTAL {{out.size}}"
  for e in [{', '.join('`' + e for e in EP)}] do
    if env.contains e then
      let axs ← liftCoreM <| collectAxioms e
      IO.println s!"ENDPOINT {{e}}: {{((axs.map toString).qsort (· < ·)).toList}}"
    else IO.println s!"ENDPOINT {{e}}: MISSING"
'''
open(f'{R}/scratch/ax/{tag}.lean', 'w').write(src)
LP = f'{R}/.lake/tcslib-check-oleans:' + ':'.join(
    f'{R}/.lake/packages/{d}/.lake/build/lib/lean' for d in sorted(os.listdir(R + '/.lake/packages')))
env = dict(os.environ, LEAN_PATH=LP, PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
p = subprocess.run(['lean', f'scratch/ax/{tag}.lean'], cwd=R, env=env, capture_output=True, text=True)
open(log, 'w').write(p.stdout + p.stderr + f'\nEXIT {p.returncode}\n')
lines = [l for l in p.stdout.splitlines() if l.startswith('AX\t')]
bad = [l for l in lines if any(a.strip() not in ('propext', 'Classical.choice', 'Quot.sound', '')
                               for a in l.split('\t')[3].strip('[]').split(','))]
print(f'exit {p.returncode}; {len(lines)} constants; outside the standard three: {len(bad)}')
for l in bad:
    print(' ', l)
for l in p.stdout.splitlines():
    if l.startswith('ENDPOINT'):
        print(l)
