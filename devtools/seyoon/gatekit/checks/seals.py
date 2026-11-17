from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).parent
import os as _os, json as _json
_GATE = Path(_os.environ['GATE']); _CFG = _json.loads((_GATE/'gate.json').read_text())
_REPO = Path(_CFG['repo']); _KIT = Path(__file__).resolve().parents[1]
r3 = _GATE/'replay'  # only read in preflight modes
worktree = _REPO
tools = worktree / 'devtools/seyoon'
out, overlay, native_source = map(Path, sys.argv[1:4])
mode = sys.argv[4]
out.mkdir()
runtime = out / 'runtime'
runtime.mkdir()
(runtime / 'lean-toolchain').write_bytes((worktree / 'lean-toolchain').read_bytes())
(runtime / '.lake').mkdir()
(runtime / '.lake/packages').symlink_to((worktree / '.lake/packages').resolve(), target_is_directory=True)
decl = (tools/'declfreeze.py').read_text().split('a = chunks(open(sys.argv[1]).read())')[0]
loc = (Path(__import__('os').environ['KIT'])/'templates/prepare_boundaries.py').read_text()  # KIT: exported by lib.sh
clean = loc[loc.index('def clean(s):'):loc.index('for idx,m in enumerate(M,1):')]
names = {}
exec(compile(decl + '\n' + clean, 'declfreeze+clean', 'exec'), names)

sim = 'TCSlib/Complexity/TuringMachine/Simulation.lean'
prim = 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean'
focus = {}  # gate 133: no unchanged probe declarations
rules = {
    'Action.apply': ('Configuration', True),
    'Cfg.inputSymbol': ('Configuration', False),
    'Cfg.workTapeSymbols': ('Configuration', False),
    'Cfg.init': ('Configuration', True),
    'MultiTapeTM.step': ('Deterministic', False),
    'MultiTapeTM.runFrom': ('Deterministic', False),
    'MultiTapeTM.initCfg': ('Deterministic', True),
    'Cfg.mapState': ('StateRenaming', False),
    'Cfg.ofWords': ('Build/Convention', False),
    'FinTM.bufferTape': ('Simulation', False),
    'FinTM.controlAction': ('Simulation', False),
    'pairEncode': ('Encoding', False),
}
guard = '''
open Lean Elab Command Meta in
run_cmd do
  let env ← getEnv
  let st ← liftTermElabM getSimpTheorems
  let targets : List Name := HEAD_NAMES
  for n in targets do
    match getReducibilityStatusCore env n with
    | .irreducible => pure ()
    | _ => throwError "NOT_IRREDUCIBLE|{n}"
    if st.toUnfold.contains n || st.isLemma (.decl n) then
      throwError "SIMP_STILL_ACTIVE|{n}"
    logInfo m!"GUARD_ACTIVE|{n}"
'''
def nlist(heads):
    return '['+', '.join(chr(96)+h for h in heads)+']'

def source(path):
    if (native_source/path).exists():
        return (native_source/path).read_text()
    assert mode.startswith('preflight')
    return (r3/'runtime'/path).read_text()

rows = []
def add(path, name, defs):
    whole = source(path)
    _, _, chunk = next(c for c in names['chunks'](whole) if c[0] == name)
    assert whole.count(chunk)==1
    start = whole.index(chunk)
    end = start + len(chunk)
    while m := re.search(r'(?m)^open [^\n]+ in\s*\n\s*\Z', whole[:start]):
        start = m.start()
    stack = []
    for line in names['clean'](whole[:end]).splitlines():
        if m := re.fullmatch(r'\s*(namespace|section|noncomputable section)(?:\s+(\S+))?\s*', line):
            stack.append(m.group(2) or '')
        elif re.fullmatch(r'\s*end(?:\s+\S+)?\s*',line):
            stack.pop()
    heads = sorted(defs)
    removed = sorted(n for n in heads if defs[n])
    attrs = 'section Gate129ReaderCheck\nattribute [local irreducible] '+' '.join(heads)+'\n'
    if removed:
        attrs += 'attribute [-simp] '+' '.join(removed)+'\n'
    code = whole[:start]+attrs+'\n'+whole[start:end]+'\n'+guard.replace('HEAD_NAMES', nlist(heads))
    code += 'end Gate129ReaderCheck\n' + ''.join('end'+(' '+s if s else '')+'\n' for s in reversed(stack))
    filename = f'Guard{len(rows)+1:03d}.lean'
    (runtime/filename).write_text(code)
    rows.append({'name': name, 'source': filename, 'owner': path,
        'owner_sha256': hashlib.sha256(whole.encode()).hexdigest(),
        'probe_sha256': hashlib.sha256(code.encode()).hexdigest(), 'heads': heads, 'simp_removed': removed})

def forced(path):
    return {'Turing.'+n: flag for n,(home,flag) in rules.items()
        if not path.endswith(home+'.lean') and (path!=sim or home in ('Configuration','Deterministic'))}

if mode == 'preflight-focus':
    for path, selected in focus.items():
        for name in selected:
            add(path, 'Turing.FinTM.'+name, forced(path))
elif mode in ('preflight-all', 'final'):
    freeze = json.loads(Path(sys.argv[5]).read_text())
    metadata = json.loads(Path(sys.argv[6]).read_text())['BOUNDARY'] if mode == 'final' else {}
    for entry in freeze['owner_source']:
        path = entry['path']
        required = set(entry['total_changed_or_added_from_campaign'])
        required.update('Turing.FinTM.'+n for n in focus.get(path, ()))
        for name, _, chunk in names['chunks'](source(path)):
            if name not in required:
                continue
            declaration = chunk.split('-/',1)[1].lstrip() if chunk.startswith('/--') else chunk
            if not re.match(r'(?:(?:private|protected|noncomputable)\s+)*(lemma|theorem)\s+', declaration):
                continue
            defs = forced(path)
            if mode == 'final' and name in metadata:
                for item in metadata[name]['foreign_definitions']:
                    if item['ordinary']:
                        defs[item['name']] = item['simp'] or item['unfold']
            if defs:
                add(path, name, defs)
else:
    raise ValueError(mode)

def write(name,data):
    (out/name).write_text(json.dumps(data, ensure_ascii=False, indent=2)+'\n')
write('REQUEST.json', {'overlay': str(overlay), 'source': str(native_source), 'mode': mode, 'rows': rows})
def run(row):
    filename = row['source']
    cmd = ['bash',str(tools/'leanelab.sh'),str(runtime),str(overlay),filename]
    p = subprocess.run(cmd,capture_output=True)
    output = p.stdout+p.stderr
    (out/(filename+'.log')).write_bytes(output)
    t = output.decode()
    active = sorted(re.findall(r'GUARD_ACTIVE\|([^\n]+)',t))
    errors = re.findall(r'^.+:\d+:\d+: error:.*$',t,re.M)
    success = p.returncode == 0 and not errors and active == row['heads']
    print(row['name'], 'PASS' if success else 'FAIL', len(errors),flush=True)
    return row | {'argv': cmd, 'verified_active_heads': active, 'pass': success,
        'exit': p.returncode, 'errors': errors, 'log_sha256': hashlib.sha256(output).hexdigest()}
with ThreadPoolExecutor(max_workers=2) as pool:
    results=list(pool.map(run,rows))
write('RESULT.json', {'pass': all(r['pass'] for r in results), 'count': len(results), 'rows': results})
sys.exit(0 if all(r['pass'] for r in results) else 1)
