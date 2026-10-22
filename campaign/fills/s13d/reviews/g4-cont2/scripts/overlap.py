import json, subprocess, sys
# usage: overlap.py <graph.json> <closure script> <outdir>
g, clo, out = sys.argv[1:4]
m = json.load(open(g))
def closure(tag, mods):
    mods = [x for x in mods if x in m]
    p = f'{out}/closure-{tag}.txt'
    subprocess.run([sys.executable, '-I', clo, g, p] + mods, check=True, capture_output=True)
    return [l.strip() for l in open(p) if l.strip()], mods
ours, _ = closure('ours-tip64', ['TCSlib/Complexity/TuringMachine/Build/ZoneRebalance'])
print('ours:', len(ours), ours)
prs = {
 '133': ['TCSlib/Complexity/TuringMachine/Build/InputDevice'],
 '134': ['TCSlib/Complexity/SpaceComplexity/WindowClock'],
 '136': ['TCSlib/Complexity/ClassNP/ExhaustiveReplay', 'TCSlib/Complexity/ClassNP', 'TCSlib/Complexity/Diagonalization/NTimeHierarchy'],
 '137': ['TCSlib/Complexity/TuringMachine/Build/InputWindow', 'TCSlib/Complexity/TuringMachine'],
 '138': ['TCSlib/Complexity/TuringMachine/Build/Rewind', 'TCSlib/Complexity/TuringMachine'],
 '139': ['TCSlib/Complexity/TuringMachine/Build/StepClock'],
}
for n, mods in prs.items():
    c, present = closure('pr' + n, mods)
    missing = [x for x in mods if x not in m]
    ov = sorted(set(c) & set(ours))
    print(f'#{n}: changed {mods} (new at the tip: {missing}); closure {len(c)} modules; overlap with ours: {ov}')
