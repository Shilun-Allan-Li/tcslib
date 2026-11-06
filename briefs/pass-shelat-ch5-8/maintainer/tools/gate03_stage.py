"""Stage one gate 03 pack's evidence at a pinned head.

usage: python3 -I gate03_stage.py <pack> <head40> <worktree-at-head> <replay-log> <checks-log> <records-repo> [--full]

<checks-log> is either the Checks.lean print log (headline prints) or, with --full, a print of every
public theorem and lemma of the pack's files (gate 03l, major 1: a headline selection can be empty).

Writes, under <records-repo>/briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence/<pack>/:
  replay.log      the replay lines of every module in the closure of the pack's files
  axioms.log      the headline axiom prints (from Checks.lean) of declarations in the pack's files
  admissions.txt  every declaration in the pack's files whose body contains `sorry`
  lint.log        scripts/style_lint.py on the pack's files
and prints the attestation block to append to the pack. Fails loudly on any replay failure.
"""
import json, os, re, subprocess, sys

pack, head, wt, replay_log, checks_log, rec = sys.argv[1:7]
full_print = sys.argv[7:] == ['--full']
src_desc = ('prints of every public theorem and lemma' if full_print else
            'headline prints from `audits/pass-shelat/Checks.lean`')
assert re.fullmatch(r'[0-9a-f]{40}', head), head
S = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
manifest = json.load(open(os.path.join(S, 'gate03', 'packs.json')))[pack]
lean = manifest['lean']
out = os.path.join(rec, 'briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence', pack)
os.makedirs(out, exist_ok=True)
assert subprocess.run(['git', '-C', wt, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip() == head

def imports(m):
    p = os.path.join(wt, m + '.lean')
    if not os.path.exists(p): return []
    return [x.replace('.', '/') for x in re.findall(r'^import\s+(\S+)', open(p, encoding='utf-8').read(), re.M)
            if x.startswith('TCSlib')]
clo, st = set(), [f[:-5] for f in lean]
while st:
    x = st.pop()
    if x in clo: continue
    clo.add(x); st += imports(x)

lines = {}
for l in open(replay_log, encoding='utf-8'):
    m = re.match(r'^(TCSlib/\S+) rc=(\d+)', l)
    if m: lines[m.group(1)] = l.rstrip('\n')
missing = sorted(m for m in clo if m not in lines)
bad = sorted(m for m in clo if m in lines and not re.search(r' rc=0 ', lines[m]))
assert not missing, ('closure modules absent from the replay log', missing)
assert not bad, ('closure modules failing in the replay log', bad)
with open(os.path.join(out, 'replay.log'), 'w', encoding='utf-8') as f:
    f.write(f'# closure of pack 03{pack}\'s files at {head}: {len(clo)} modules, extracted from {os.path.basename(replay_log)}\n')
    for m in sorted(clo): f.write(lines[m] + '\n')
sorry_warn = sum(int(re.search(r'sorry=(\d+)', lines[m]).group(1)) for m in clo)

decl = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private |protected |noncomputable )*)(theorem|lemma|def|abbrev|instance|structure|inductive)\s+(\S+)')
names, adm = {}, []
for f in lean:
    L = open(os.path.join(wt, f), encoding='utf-8').read().split('\n'); ns = []; cur = None
    for i, l in enumerate(L, 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        m = decl.match(l)
        if m:
            n3 = m.group(3)
            full = n3[len('_root_.'):] if n3.startswith('_root_.') else '.'.join(ns + [n3]); cur = (full, f, i)
            if 'private' not in m.group(1): names[full] = f
        if re.search(r'\bsorry\b', l) and not l.strip().startswith('--') and cur and (not adm or adm[-1] != cur):
            adm.append(cur)
ax = []
txt = open(checks_log, encoding='utf-8').read()
for m in re.finditer(r"'(\S+?)' (does not depend on any axioms|depends on axioms: \[([^\]]*)\])", txt):
    if m.group(1) in names: ax.append((m.group(1), (m.group(3) or '').replace('\n', ' ')))
with open(os.path.join(out, 'axioms.log'), 'w', encoding='utf-8') as f:
    f.write(f'# axiom {src_desc} for declarations in pack 03{pack}\'s files, at {head}\n')
    for n, a in ax: f.write(f'{n}: {a or "none"}\n')
with open(os.path.join(out, 'admissions.txt'), 'w', encoding='utf-8') as f:
    f.write(f'# declarations with `sorry` in pack 03{pack}\'s files, at {head}\n')
    for n, fl, i in adm: f.write(f'{fl}:{i} {n}\n')
lint = subprocess.run([sys.executable, '-I', 'scripts/style_lint.py', *lean], cwd=wt, capture_output=True, text=True)
with open(os.path.join(out, 'lint.log'), 'w', encoding='utf-8') as f:
    f.write(f'# scripts/style_lint.py on pack 03{pack}\'s files, at {head}\n' + lint.stdout + lint.stderr)
nsorry_ax = sum(1 for _, a in ax if 'sorryAx' in a)
nstd = sum(1 for _, a in ax if set(x.strip() for x in a.split(',') if x.strip()) <= {'propext', 'Classical.choice', 'Quot.sound'})
ax_line = ('not applicable (no declaration selected).' if not ax else
           f'''{len(ax)} {src_desc} in this pack's files:
   {nstd} use only the standard axioms, and {nsorry_ax} depend on `sorryAx`; any other axiom is listed
   in the log.''')
print(f'''### Attestation results at `{head}` (evidence under `evidence/{pack}/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, {len(clo)} modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   {sorry_warn} `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): {ax_line}
3. **Admissions** (`admissions.txt`): {len(adm)} declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: {next((l for l in (lint.stdout + lint.stderr).splitlines() if re.match(r'\d+ findings? in \d+ files?', l.strip())), 'no summary line')}.
''')
