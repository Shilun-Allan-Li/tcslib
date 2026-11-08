#!/usr/bin/env python3
"""Post-processing of the final verification chain (python only; no Lean).
python3 -I final_post.py <head-sha>
Writes evidence/logs/final-summary.json and the comparison files named below."""
import sys, os, json, re, subprocess, collections, hashlib, tarfile
H = sys.argv[1]
A = '1aa5506f58f77c215e56d24311ec33bd931cacf1'
CP = '/workspace/cp2'; SRC = f'{CP}/src'; EV = f'{CP}/evidence'; L = f'{EV}/logs'; T = f'{CP}/tools'
PACK = '/workspace/tcslib/outbox/fills/cleanup-part2/inputs'
def run(*a):
    r = subprocess.run(['python3', '-I', *a], capture_output=True, text=True)
    return r.stdout + r.stderr
out = {'head': H, 'ancestor': A}

# 1. replay reconciliation: every affected module PASS at the final source bytes
recs = [json.loads(l) for l in open(f'{L}/checks-final.jsonl')]
aff = [l.strip() for l in open(f'{L}/affected-final.txt') if l.strip()]
# delta replay (modules affected by the commits after the full replay's head) overrides
if os.path.exists(f'{L}/checks-final-delta.jsonl'):
    recs += [json.loads(l) for l in open(f'{L}/checks-final-delta.jsonl')]
    aff += [m for m in (l.strip() for l in open(f'{L}/affected-final-delta.txt')) if m and m not in set(aff)]
last = {}
for r in recs: last[r.get('module') or r.get('rel')] = r
def sha_at(rev, path):
    b = subprocess.run(['git', '-C', SRC, 'show', f'{rev}:{path}'], capture_output=True).stdout
    return hashlib.sha256(b).hexdigest()
bad = []
for m in aff + ['TCSlib', 'audits/pass-shelat/Checks']:
    r = last.get(m)
    p = m + '.lean'
    if r is None: bad.append((m, 'no record')); continue
    ok = r.get('status') == 'PASS' and r.get('rc') == 0 and r.get('parsed_errors') == 0 and \
        r.get('object_fresh_nonempty') is True
    if not ok: bad.append((m, 'not PASS')); continue
    if r.get('source_sha256') and r['source_sha256'] != sha_at(H, p): bad.append((m, 'source sha differs'))
out['replay'] = {'affected': len(aff), 'records': len(recs), 'failures_or_mismatch': bad,
                 'all_pass_at_head_bytes': not bad}
# unaffected modules: source unchanged since the ancestor and not importing a changed module
order = [l.strip() for l in open(f'{L}/order-final.txt') if l.strip()]
unaff = [m for m in order if m not in set(aff)]
chg = [m for m in unaff if sha_at(A, m + '.lean') != sha_at(H, m + '.lean')]
out['unaffected'] = {'count': len(unaff), 'source_changed_since_ancestor': chg}

# 2. Checks axioms vs baseline
CHK = f'{L}/final-delta/modules/audits/pass-shelat/Checks.log'
if not os.path.exists(CHK): CHK = f'{L}/final/modules/audits/pass-shelat/Checks.log'
out['checks_log'] = CHK
run(f'{T}/axcmp.py', f'{L}/baseline/modules/audits/pass-shelat/Checks.log', CHK,
    f'{L}/axioms-checks-final-vs-baseline.json')
ck = json.load(open(f'{L}/axioms-checks-final-vs-baseline.json'))
out['checks_axioms'] = {'multisets_equal': ck['multisets_equal'], 'base_records': ck['base']['records'],
                        'head_records': ck['head']['records'], 'head_sorryAx': ck['head']['sorryAx_records']}

# 3. census axioms and C3 vs baseline
print(run(f'{T}/census_axcmp.py', f'{EV}/census/baseline/axioms.tsv', f'{EV}/census/final/axioms.tsv',
          f'{L}/census-axioms-final-vs-baseline.json')[-1500:])
print(run(f'{T}/c3cmp.py', f'{EV}/census/baseline/c3.tsv', f'{EV}/census/final/c3.tsv',
          f'{L}/c3-final-vs-baseline.json')[-1500:])

# 4. C3 metadata controls
rows = [l.rstrip('\n').split('\t') for l in open(f'{EV}/census/c3controls/c3.tsv') if l.startswith('C3\t')]
pos = [r for r in rows if r[2] == 'cp2_c3_pos']; neg = [r for r in rows if r[2] == 'cp2_c3_neg']
out['c3_controls'] = {'pos_rows': pos, 'neg_rows': neg,
                      'pass': len(pos) >= 1 and all(r[5] == 'Turing.pairDecode' and r[6] == 'TCSlib.Complexity.TuringMachine.Encoding' for r in pos) and not neg}

# 5. sensitivity controls
def errs(log):
    t = open(log).read()
    return [(int(m.group(1)), m.group(3)) for m in re.finditer(r'\.lean:(\d+):(\d+): error[^:]*: ?(.*)', t)], ('CP2-EOF' in t)
ctl_src = open(f'{T}/lean/Controls.lean.txt').read().split('\n')
sites = {int(i) + 1: re.search(r'CP2-SITE (\w+)', l).group(1) for i, l in enumerate(ctl_src) if 'CP2-SITE' in l}
ue, _ = errs(f'{L}/controls-final2/modules/.lake/cleanup-part2-probes/controls/ControlsUnsealed.log')
sealed = open(f'{SRC}/.lake/cleanup-part2-probes/controls/ControlsSealed.lean').read().split('\n')
end = next(i for i, l in enumerate(sealed) if l == '-- CP2 END SEAL') + 1
w0 = next(i for i, l in enumerate(sealed) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1
off = end - w0 + 2
se, seof = errs(f'{L}/controls-final2/modules/.lake/cleanup-part2-probes/controls/ControlsSealed.log')
harness = [e for e in se if e[0] <= end]
mapped = [(ln - off, msg) for ln, msg in se if ln > end]
hit = collections.defaultdict(list)
stray = []
for ln, msg in mapped:
    if ln in sites: hit[sites[ln]].append(msg)
    else: stray.append((ln, msg))
negs = sorted(v for v in sites.values())
out['controls'] = {'unsealed_errors': ue, 'sealed_harness_errors': harness, 'sealed_eof': seof,
                   'negatives_failing_at_site': {k: hit.get(k, []) for k in negs},
                   'sealed_errors_off_site': stray,
                   'pass': not ue and not harness and seof and all(hit.get(k) for k in negs) and not stray}

# 6. seals: standard and strict, summaries
def ssum(phase):
    d = json.load(open(f'{L}/seal-{phase}.json'))
    return {'files': len(d), 'valid': sum(1 for v in d.values() if v['valid']),
            'requests': sum(v['requests'] for v in d.values()), 'active': sum(v['active'] for v in d.values()),
            'already_irreducible': sum(v['already_irreducible'] for v in d.values()),
            'files_failing': sum(1 for v in d.values() if v['error_diagnostics']),
            'failing_declarations': sum(len(v['failing_declarations']) for v in d.values()),
            'error_diagnostics': sum(v['error_diagnostics'] for v in d.values()),
            'notation_unsealed': sorted({v.get('notation_unsealed') or '' for v in d.values()})}
out['seal_standard_final'] = ssum('final'); out['seal_strict_final'] = ssum('final-strict')
out['seal_strict_baseline'] = ssum('baseline'); out['seal_standard_j2'] = ssum('j2')
json.dump({k: out[k] for k in out if k.startswith('seal_')}, open(f'{L}/seal-final-summary.json', 'w'), indent=1)

# 7. explicit scan at the head with the final name table
cons = [l.strip() for l in open(f'{PACK}/consumer-files.txt') if l.strip()]
os.chdir(SRC)
print(run(f'{T}/explicit_scan.py', f'{EV}/census/final/names.tsv', f'{L}/explicit-scan-final.json', *cons)[-400:])
sc = json.load(open(f'{L}/explicit-scan-final.json'))
out['explicit_scan'] = {'summary': sc['summary'],
                        'foreign_or_core_defs': [it for it in sc['items'] if it['class'] in
                                                 ('FOREIGN_TCS_DEF', 'CORE_MATHLIB_DEF', 'FOREIGN_TCS_DEF?AMBIGUOUS')]}

# 8. residual classification and dispositions
print(run(f'{T}/classify_residual.py', 'final', f'{EV}/maps/residual-final.json', f'{EV}/maps/residual-final.md'))
print(run(f'{T}/dispositions.py', H, f'{L}/seal-final.json', f'{L}/seal-final-strict.json',
          f'{L}/explicit-scan-final.json', f'{EV}/census/final/c3.tsv', f'{EV}/census/final/axioms.tsv',
          f'{EV}/maps/residual-final.json', f'{EV}/maps/dispositions-final.json')[-3000:])

# 9. archive the final seal probe sources
for ph in ('final', 'final-strict'):
    with tarfile.open(f'{EV}/probes/seal-{ph}-probes.tar.xz', 'w:xz') as tf:
        tf.add(f'{SRC}/.lake/cleanup-part2-probes/seal/{ph}', arcname=f'seal-{ph}')
for f in ('controls/ControlsSealed.lean', 'controls/ControlsUnsealed.lean', 'census/FinalCensus.lean',
          'census/FinalCensus2.lean', 'census/C3Controls.lean'):
    b = open(f'{SRC}/.lake/cleanup-part2-probes/{f}').read()
    open(f'{EV}/probes/{os.path.basename(f)[:-5]}.source.txt', 'w').write(b)
json.dump(out, open(f'{L}/final-summary.json', 'w'), indent=1, default=str)
print(json.dumps({k: v for k, v in out.items() if k not in ('explicit_scan',)}, indent=1, default=str)[:6000])
