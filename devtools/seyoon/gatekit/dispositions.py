"""Classify the copy-screen delta ($GATE/screen/pairdiff.txt) into screen/PAIR-DISPOSITIONS.json.
Every NEW or GONE pair needs a disposition in $GATE/pair-notes.json, keyed "STATUS|target|source",
with the value [class, note] (for example ["threshold", "why the text crosses half"]).
An unclassified pair stops the script."""
import json, os, re
from pathlib import Path
G = Path(os.environ['GATE'])
notes = json.loads((G/'pair-notes.json').read_text()) if (G/'pair-notes.json').exists() else {}
rx = re.compile(r'^\s+(NEW|GONE)\s+(\S+)\s+reproduces\s+(\S+): (\d+)/(\d+) = (\d+)%')
rows = []
for line in (G/'screen/pairdiff.txt').read_text().splitlines():
    m = rx.match(line)
    if not m: continue
    st, tgt, src, ch, sch, pct = m.groups()
    c = notes.get(f'{st}|{tgt}|{src}')
    if c is None: raise SystemExit('unclassified (add it to pair-notes.json): ' + line)
    rows.append({'status': st, 'target': tgt, 'source': src, 'chars': int(ch), 'source_chars': int(sch),
                 'pct': int(pct), 'class': c[0], 'note': c[1]})
first = lambda p: (G/p).read_text().splitlines()[0].strip()
pairs = lambda s: re.search(r'copy pairs[^:]*: (\d+)', s).group(1)
b, h = first('screen/BASE/screen.txt'), first('screen/HEAD/screen.txt')
d = {'base_summary': b, 'head_summary': h,
     'population_base': (G/'POPULATION-BASE.txt').read_text().split(), 'population_head': (G/'POPULATION.txt').read_text().split(),
     'new': sum(r['status'] == 'NEW' for r in rows), 'gone': sum(r['status'] == 'GONE' for r in rows),
     'net_directed_pairs': f'{pairs(b)} -> {pairs(h)}', 'pairs': rows}
(G/'screen/PAIR-DISPOSITIONS.json').write_text(json.dumps(d, ensure_ascii=False, indent=1) + '\n')
print(d['new'], 'new', d['gone'], 'gone', d['net_directed_pairs'])
