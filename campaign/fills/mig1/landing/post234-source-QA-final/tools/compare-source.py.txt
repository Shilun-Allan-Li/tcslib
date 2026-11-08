"""Maintainer-owned source-only checkpoint parser. Adapted after reading cp03's
maintainer parser; no payload script is imported or executed. Complete declaration
headers honor binder depth, so `(input := x)` is never a proof delimiter."""
from pathlib import Path
import re, json, hashlib, difflib
OUT=Path(__file__).resolve().parent
REPO=OUT.parents[4]
BASE='83ac315ed9e7089466bd16a32f3b71fbadc556d2'
FILES=(REPO/'campaign/fills/mig1/inputs/owned-files.txt').read_text().splitlines()
CP03=OUT.parent/'checkpoint03-2026-11-07'
CP05=OUT.parent/'checkpoint05-2026-11-07/cp05/fill-mig1-mega-cp05'
CP07=OUT/'extracted/fill-mig1-mega-cp07'

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


def exact_patch(text,state,reverse=False):
    """Apply/reverse unified text hunks in memory, checking every context byte/count."""
    lines=text.splitlines(keepends=True); i=0; changed=[]
    match=re.match(r'From ([0-9a-f]{40}) ',lines[0]); assert match
    while i<len(lines):
        m=re.match(r'diff --git a/(\S+) b/(\S+)\n',lines[i])
        if not m:i+=1;continue
        a,b=m.groups();assert a==b and a in FILES,(a,b)
        old=state[a].splitlines(keepends=True);new=[];pos=0;i+=1;hunks=0
        while i<len(lines) and not lines[i].startswith('diff --git '):
            h=re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@',lines[i])
            if not h:i+=1;continue
            start,count,nstart,ncount=[int(x) if x is not None else 1 for x in h.groups()]
            if reverse:start,count,nstart,ncount=nstart,ncount,start,count
            assert start-1>=pos,(a,start,pos)
            new.extend(old[pos:start-1]);pos=start-1;assert len(new)==nstart-1,(a,nstart,len(new))
            consumed=produced=0;i+=1;hunks+=1
            while i<len(lines) and (consumed<count or produced<ncount):
                line=lines[i];tag=line[0];assert tag in ' +-',line
                if reverse:tag={'+':'-','-':'+',' ':' '}[tag]
                if tag in ' -':
                    assert pos<len(old) and old[pos]==line[1:],(a,pos+1,old[pos] if pos<len(old) else '',line)
                    pos+=1;consumed+=1
                if tag in ' +':new.append(line[1:]);produced+=1
                i+=1
            assert consumed==count and produced==ncount
        assert hunks;new.extend(old[pos:]);state[a]=''.join(new);changed.append(a)
    return {'declared_commit_header':match.group(1),'paths':changed,'exact_hunks':True,'reverse':reverse}

def snapshot(root):
    return {f:(root/'source'/(f+'.txt')).read_text() for f in FILES}

def main():
    oldroot=CP03/'cp03/fill-mig1-mega-cp03';cp03=snapshot(oldroot)
    prior=json.loads((CP03/'source-comparison.json').read_text())
    assert prior['base']==BASE
    for f,s in cp03.items():assert hashlib.sha256(s.encode()).hexdigest()==prior['checkpoints']['cp03'][f]['sha256'],f
    base=cp03.copy();reverse=[]
    patches=sorted((oldroot/'patches').glob('*.patch'))
    for p in reversed(patches):reverse.append({'path':p.name,**exact_patch(p.read_text(),base,True)})
    roundtrip=base.copy()
    for p in patches:exact_patch(p.read_text(),roundtrip)
    assert roundtrip==cp03
    cp07=snapshot(CP07);reconstructed=base.copy();forward=[]
    for p in sorted((CP07/'patches').glob('*.patch')):forward.append({'path':p.name,**exact_patch(p.read_text(),reconstructed)})
    assert reconstructed==cp07,'cp07 snapshots differ from cumulative exact patch reconstruction'
    assert forward[-1]['declared_commit_header']==(CP07/'HEAD.txt').read_text().strip()
    assert (CP07/'BASE.txt').read_text().strip()==BASE
    bundle=(CP07/'fill-mig1-mega.bundle').read_bytes();bundlehead=bundle[:bundle.index(b'\n\n')].decode();assert BASE in bundlehead and forward[-1]['declared_commit_header'] in bundlehead
    summary={'base':BASE,'method':'No Git or payload tooling: reverse reviewed cp03 patches after validating all snapshot hashes, forward-roundtrip cp03, then exact in-memory cp07 patch replay; comment-aware depth-aware declaration freeze. Source only.','base_reverse':reverse,'cp03_roundtrip_exact':True,'cp07_patches':forward,'cp07_patch_snapshots_exact':True,'bundle_header':bundlehead,'bundle_limitation':'Pack objects not imported or validated as Git objects; full head values are supplied metadata.','comparisons':{}}
    versions={'base':base,'cp03':cp03,'cp07':cp07}
    if CP05.exists():versions['cp05']=snapshot(CP05)
    for left,right in [('base','cp07'),('cp03','cp07'),('cp05','cp07')]:
        if left not in versions:continue
        results={};diff=[]
        for f in FILES:
            a,b=versions[left][f],versions[right][f];item=compare(a,b);item['changed']=a!=b;item['source_sha256']=hashlib.sha256(b.encode()).hexdigest();item['base_sha256']=hashlib.sha256(a.encode()).hexdigest();results[f]=item
            diff.extend(difflib.unified_diff(a.splitlines(keepends=True),b.splitlines(keepends=True),fromfile=left+'/'+f,tofile=right+'/'+f))
        summary['comparisons'][left+'-to-'+right]=results;(OUT/(left+'-to-'+right+'.diff')).write_text(''.join(diff))
    target_results=[]
    for target in json.loads((REPO/'campaign/fills/mig1/inputs/target-admissions.json').read_text()):
        am={d['name']:d for d in decls(base[target['path']])};bm={d['name']:d for d in decls(cp07[target['path']])};a,b=am[target['name']],bm[target['name']]
        target_results.append({'name':target['name'],'path':target['path'],'line':b['start'],'end':b['end'],'header_unchanged':a['header']==b['header'],'source_proof_filled':not re.search(r'\b(?:sorry|admit)\b',b['code'])})
    expected=decls((REPO/'campaign/fills/mig1/inputs/forwarding-map-contract.lean.txt').read_text());actual={d['name']:d for d in decls(cp07['TCSlib/Complexity/TuringMachine/Build/Primitives.lean'])}
    forwarding=[{'name':d['name'],'header_matches_gate':d['header']==actual[d['name']]['header'],'line':actual[d['name']]['start'],'source_proof_filled':not re.search(r'\b(?:sorry|admit)\b',actual[d['name']]['code'])} for d in expected]
    summary['target_results']=target_results;summary['forwarding_results']=forwarding
    current=summary['comparisons']['base-to-cp07'];adds=[n for f,x in current.items() for n in x['public_added']];removes=[n for f,x in current.items() for n in x['public_removed']]
    summary['freeze_summary']={'public_before':sum(x['public_counts'][0] for x in current.values()),'public_after':sum(x['public_counts'][1] for x in current.values()),'public_added':adds,'public_removed':removes,'header_changes':[(f,n) for f,x in current.items() for n in x['public_header_changes']],'definition_changes':[(f,n) for f,x in current.items() for n in x['public_definition_changes']],'visibility_changes':[(f,n) for f,x in current.items() for n in x['visibility_changes']],'order_changes':[f for f,x in current.items() if not x['public_order_unchanged']],'imports_changed':{f:{'before':x['imports_before'],'after':x['imports_after']} for f,x in current.items() if x['imports_before']!=x['imports_after']},'changed_public_proofs':sum(len(x['public_proof_changes']) for x in current.values()),'admissions':[(f,d) for f,x in current.items() for d in x['admissions']]}
    (OUT/'source-comparison.json').write_text(json.dumps(summary,indent=2)+'\n')
    (OUT/'base-source').mkdir(exist_ok=True)
    for f,s in base.items():p=OUT/'base-source'/(f+'.txt');p.parent.mkdir(parents=True,exist_ok=True);p.write_text(s)
    print(json.dumps(summary['freeze_summary'],indent=2));print('All17:',len(target_results),all(x['source_proof_filled'] and x['header_unchanged'] for x in target_results));print('Forwarding:',forwarding)
    for version in ['cp03','cp05']:
        key=version+'-to-cp07'
        if key in summary['comparisons']:print(version+' changes:',[f for f,x in summary['comparisons'][key].items() if x['changed']])

if __name__=='__main__':main()
