"""The round-3 population: round 1's 214 labelled files, plus the modules that entered the 73 added
files' upstream import closure since (at the base; and by the payback, at the landed tree).
Asserts that pop3.txt is exactly that union. usage: python3 -I popcheck.py <graph-base.json>
<graph-landed.json> <round1-labels.tsv> <added.txt> <pop3.txt>"""
import json, sys
gb, gl = json.load(open(sys.argv[1])), json.load(open(sys.argv[2]))
r1 = {l.split('\t')[1] for l in open(sys.argv[3], encoding='utf-8')}
added = [l.strip()[:-5] for l in open(sys.argv[4]) if l.strip()]
pop = {l.strip() for l in open(sys.argv[5]) if l.strip()}
def up(g):
    need = set()
    def v(m):
        if m in need: return
        need.add(m)
        for d in g.get(m, []):
            if d in g: v(d)
    for t in added: v(t)
    return {m + '.lean' for m in need}
cb, cl = up(gb), up(gl)
print(f'closure of the 73 added files: {len(cb)} modules at the base, {len(cl)} at the landed tree')
print('in the base closure, not in round 1\'s population:', sorted(cb - r1))
print('added to the closure by the payback:', sorted(cl - cb))
print('round 1 population files outside both closures (round 1 named them: TQBF, Path, ImmermanSzelepcsenyi, Savitch and the supplement\'s four):', sorted(r1 - cb - cl))
want = r1 | cb | cl
assert pop == want, (sorted(pop - want), sorted(want - pop))
print(f'pop3.txt = round 1 population ({len(r1)}) + {len(want) - len(r1)} = {len(pop)} files: OK')
