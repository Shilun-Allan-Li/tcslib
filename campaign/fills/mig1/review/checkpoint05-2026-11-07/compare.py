"""Independent source-only comparison; never imports or executes payload tooling."""
from __future__ import annotations
import difflib
import hashlib
import json
from pathlib import Path
import re
import sys
import importlib.util
sys.dont_write_bytecode=True

OUT = Path(__file__).resolve().parent
REPO = OUT.parents[4]
BASE = json.loads((REPO / 'campaign/fills/mig1/dispatch.json').read_text())['lean_base']
FILES = (REPO / 'campaign/fills/mig1/inputs/owned-files.txt').read_text().splitlines()


def clean(text):
    """Remove nested comments while retaining newlines and string contents."""
    a = list(text); i = 0; depth = 0; string = False
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                a[i:i+2] = '  '; i += 2; depth += 1
            elif text.startswith('-/', i):
                a[i:i+2] = '  '; i += 2; depth -= 1
            else:
                if a[i] != '\n': a[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\': i += 2
            elif text[i] == '"': string = False; i += 1
            else: i += 1
        elif text.startswith('/-', i):
            a[i:i+2] = '  '; i += 2; depth = 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n': a[i] = ' '; i += 1
        elif text[i] == '"': string = True; i += 1
        else: i += 1
    assert depth == 0 and not string
    return ''.join(a)


def norm(text): return ' '.join(text.split())


def header(text):
    stack = []; i = 0; string = False
    while i < len(text):
        c = text[i]
        if string:
            if c == '\\': i += 2; continue
            if c == '"': string = False
        elif c == '"': string = True
        elif c in '([{⟨': stack.append(c)
        elif c in ')]}⟩':
            assert stack and '([{⟨'.index(stack[-1]) == ')]}⟩'.index(c), text[:i]
            stack.pop()
        elif not stack:
            if text.startswith(':=', i): break
            if re.match(r'where\b', text[i:]) and (i == 0 or text[i-1].isspace()): break
            if c == '\n' and re.match(r'\n\s*\|', text[i:]): break
        i += 1
    return norm(text[:i])


DECL = re.compile(r'^(?P<attrs>(?:@\[[^\]]*\]\s*)*)(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)(?P<kind>theorem|lemma|def|abbrev|instance|structure|inductive|class)\b\s*(?P<name>[^\s(:{\[]+)?')
STOP = re.compile(r'^(?:end\b|namespace\b|(?:noncomputable\s+)?section\b|mutual\b|open\b|variable\b|set_option\b|#|attribute\b|universe\b)')


def decls(text):
    c = clean(text); lines = c.splitlines(keepends=True); rawlines = text.splitlines(keepends=True)
    stack = []; results = []; current = None; seen = {}; pending_attr = None
    def close(end):
        nonlocal current
        if current:
            d = current; d['code'] = ''.join(lines[d['start']-1:end]); d['header'] = header(d['code'])
            d['raw'] = ''.join(rawlines[d['start']-1:end]); d['end'] = end
            if d['name'] is None: d['name'] = 'instance⟨' + d['header'] + '⟩'
            n = seen.get(d['name'], 0) + 1; seen[d['name']] = n
            if n != 1: d['name'] += '#' + str(n)
            results.append(d)
        current = None
    for i, l in enumerate(lines):
        m = DECL.match(l)
        if m:
            close(pending_attr if pending_attr is not None else i)
            ns = '.'.join(n for k,n in stack if k == 'namespace')
            name = m['name']
            if name:
                name = name.removeprefix('_root_.') if name.startswith('_root_.') else (ns + '.' + name if ns else name)
            current = dict(name=name, private='private' in m['mods'].split(), kind=m['kind'], start=(pending_attr if pending_attr is not None else i)+1)
            pending_attr = None
        elif l.startswith('@['):
            if pending_attr is None: pending_attr = i
        elif STOP.match(l):
            close(i); pending_attr = None
            if l.startswith('namespace '): stack.extend(('namespace', n) for n in l.split()[1].split('.'))
            elif re.match(r'(?:noncomputable\s+)?section\b', l):
                s = re.match(r'(?:noncomputable\s+)?section\b\s*(\S*)',l)
                stack.append(('section', s.group(1)))
            elif l.startswith('mutual'): stack.append(('mutual', ''))
            elif l.startswith('end'):
                endname = l.split()[1] if len(l.split()) > 1 else ''
                if not endname:
                    if stack: stack.pop()
                else:
                    for n in reversed(endname.split('.')):
                        assert stack and stack[-1][1] == n, (l, stack)
                        stack.pop()
        elif pending_attr is not None and l.strip():
            # All standalone attributes in the owned sources are on one line.
            raise AssertionError(('unexpected multiline attribute', i+1, l))
    close(len(lines))
    return results


def imports(s): return [x for x in clean(s).splitlines() if re.match(r'^import\s', x)]


def compare(a, b):
    ad, bd = decls(a), decls(b); am = {d['name']:d for d in ad}; bm = {d['name']:d for d in bd}
    ap = [d['name'] for d in ad if not d['private']]; bp = [d['name'] for d in bd if not d['private']]
    common = [n for n in ap if n in bm and not bm[n]['private']]
    result = dict(public_counts=[len(ap),len(bp)], private_counts=[len(ad)-len(ap),len(bd)-len(bp)],
        public_added=[n for n in bp if n not in am],public_removed=[n for n in ap if n not in bm],
        visibility_changes=[n for n in am.keys() & bm.keys() if am[n]['private'] != bm[n]['private']],
        public_order_unchanged=common == [n for n in bp if n in am and not am[n]['private']],
        public_header_changes=[n for n in common if am[n]['header'] != bm[n]['header']],
        public_definition_changes=[n for n in common if bm[n]['kind'] not in ('theorem','lemma') and norm(am[n]['code']) != norm(bm[n]['code'])],
        public_proof_changes=[dict(name=n,line=bm[n]['start'],end=bm[n]['end']) for n in common if bm[n]['kind'] in ('theorem','lemma') and norm(am[n]['code']) != norm(bm[n]['code'])],
        private_added=[d['name'] for d in bd if d['private'] and d['name'] not in am],
        private_removed=[d['name'] for d in ad if d['private'] and d['name'] not in bm],
        private_changed=[dict(name=d['name'],line=d['start'],end=d['end']) for d in bd if d['private'] and d['name'] in am and norm(d['code']) != norm(am[d['name']]['code'])],
        imports_before=imports(a),imports_after=imports(b),
        admissions=[dict(name=d['name'],line=d['start']) for d in bd if re.search(r'\bsorry\b',d['code'])])
    return result


def main():
    spec=importlib.util.spec_from_file_location('pinned_source',OUT/'pinned_source.py')
    pinned=importlib.util.module_from_spec(spec);spec.loader.exec_module(pinned)
    bases=pinned.base_sources()
    allresults = {'base':BASE,'method':'Independent comment-aware declaration census and delimiter-depth complete header comparison; static source only. No payload tooling executed.','checkpoints':{},'base_source_method':'Pinned base reconstructed in memory by reversing already reviewed cp02 patches; round trip checked; no Git invocation.'}
    for cp in ('cp05',):
        r = {}; diff = []
        for f in FILES:
            a = bases[f]
            b = (OUT/cp/('fill-mig1-mega-'+cp)/'source'/(f+'.txt')).read_text()
            r[f] = compare(a,b)
            r[f]['sha256'] = hashlib.sha256(b.encode()).hexdigest()
            r[f]['changed'] = a != b
            diff.extend(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile='base/'+f,tofile=cp+'/'+f))
        allresults['checkpoints'][cp] = r
        (OUT/(cp+'-source.diff')).write_text(''.join(diff))
    progression = {}
    for f in FILES:
        a=(OUT.parent/'checkpoint03-2026-11-07'/'cp03'/'fill-mig1-mega-cp03'/'source'/(f+'.txt')).read_text()
        b=(OUT/'cp05'/'fill-mig1-mega-cp05'/'source'/(f+'.txt')).read_text()
        if a != b: progression[f]=compare(a,b)
    allresults['progression'] = progression
    p1=next(p for p in (OUT.parent/'checkpoint03-2026-11-07'/'cp03'/'fill-mig1-mega-cp03'/'patches').iterdir() if p.name.startswith('0001')).read_text()
    p2=next(p for p in (OUT/'cp05'/'fill-mig1-mega-cp05'/'patches').iterdir() if p.name.startswith('0001')).read_text()
    allresults['first_patch_metadata_diff'] = list(difflib.unified_diff(p1.splitlines(),p2.splitlines(),n=2))
    (OUT/'source-comparison.json').write_text(json.dumps(allresults,indent=2)+'\n')
    for cp, files in allresults['checkpoints'].items():
        print(cp)
        for f,r in files.items():
            if r['changed']:
                print(f, 'public',r['public_counts'],'proof changes',len(r['public_proof_changes']),'private additions',len(r['private_added']))
            for k in ('public_removed','visibility_changes','public_header_changes','public_definition_changes'):
                assert not r[k], (cp,f,k,r[k])
            expected_additions=['Turing.FinTM.pairMapSndTM','Turing.FinTM.pairMapSndTM_computes','Turing.FinTM.pairMapSndTM_spaceUsed'] if f == 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean' else []
            assert r['public_added']==expected_additions,(cp,f,r['public_added'])
            assert r['public_order_unchanged']
            if r['imports_before'] != r['imports_after']:
                assert f == 'TCSlib/Complexity/TuringMachine/Simulation.lean'
                assert [i for i in r['imports_after'] if i not in r['imports_before']] == ['import Mathlib.Algebra.BigOperators.Fin']
                assert all(i in r['imports_after'] for i in r['imports_before'])
        print('admissions:',sum(len(r['admissions']) for r in files.values()))
    print('first patch difference:',allresults['first_patch_metadata_diff'])
    print('PASS (static freeze only)')


if __name__ == '__main__': main()
