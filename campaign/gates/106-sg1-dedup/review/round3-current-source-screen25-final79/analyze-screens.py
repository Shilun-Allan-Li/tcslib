from pathlib import Path
import collections, json, re

OUT = Path(__file__).resolve().parent

def parse(side):
    text = (OUT / (side + '.out')).read_text()
    summary = re.fullmatch(r'declarations screened: (\d+); copy pairs \(target reproduces >= half of source\): (\d+); reproduced text: ([\d,]+) chars', text.splitlines()[0])
    assert summary
    index = {r['label']:r for r in json.loads((OUT / (side + '-index.json')).read_text())}
    rows = []
    for line in text.splitlines()[1:]:
        match = re.fullmatch(r'\s+(.+?)  reproduces  (.+?): (\d+)/(\d+) = (\d+)%', line)
        assert match, line
        a,b,shared,denominator,percent = match.groups()
        assert a in index and b in index and index[a]['kind'] == index[b]['kind']
        assert int(denominator) == index[b]['body_chars']
        rows.append(dict(a=a, b=b, shared=int(shared), denominator=int(denominator), printed_percent=int(percent),
                         kind=index[a]['kind'], cross_file=index[a]['path'] != index[b]['path']))
    assert len(rows) == int(summary[2]) and len(index) == int(summary[1])
    assert sum(r['shared'] for r in rows) == int(summary[3].replace(',',''))
    assert len({(r['a'],r['b']) for r in rows}) == len(rows)
    (OUT / (side + '-candidates.json')).write_text(json.dumps(rows, indent=2) + '\n')
    return rows, dict(declarations=int(summary[1]), candidates=len(rows), reproduced_chars=sum(r['shared'] for r in rows),
                     by_kind_location=dict(collections.Counter(r['kind'] + ('/cross-file' if r['cross_file'] else '/in-file') for r in rows)))

def main():
    base, bs = parse('base'); head, hs = parse('head')
    a={(r['a'],r['b']):r for r in base}; b={(r['a'],r['b']):r for r in head}
    new=[b[k] for k in sorted(b.keys()-a.keys())]; gone=[a[k] for k in sorted(a.keys()-b.keys())]
    changed=[dict(base=a[k], head=b[k]) for k in sorted(a.keys()&b.keys()) if a[k] != b[k]]
    delta=dict(base=bs, head=hs, new=new, gone=gone, changed_measurements=changed,
               direction='Raw tool: a reproduces b; denominator is the complete normalized b body. Directed rows are not independent semantic proof copies.')
    (OUT/'pair-delta.json').write_text(json.dumps(delta, indent=2)+'\n')
    text=[f'Base {bs["candidates"]}; head {hs["candidates"]}; new {len(new)}; gone {len(gone)}; changed retained {len(changed)}.']
    for label, rows in [('NEW',new),('GONE',gone)]:
        for r in rows:text.append(f'{label} {r["a"]} reproduces {r["b"]}: {r["shared"]}/{r["denominator"]} = {r["printed_percent"]}%')
    (OUT/'pair-delta.out').write_text('\n'.join(text)+'\n')
    print(json.dumps(dict(base=bs,head=hs,new=len(new),gone=len(gone),changed_measurements=len(changed)),indent=2))
    print('\n'.join(text))

if __name__ == '__main__':
    main()
