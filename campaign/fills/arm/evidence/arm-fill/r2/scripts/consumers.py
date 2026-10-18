"""Direct importers (outside the component) of each received component, from the tip's import
graph (imports.py output). Component = a list of module path prefixes.
usage: python3 -I consumers.py <graph.json>"""
import json, sys
g = json.load(open(sys.argv[1]))
SC = 'TCSlib/Complexity/SpaceComplexity/'; PS = 'TCSlib/Complexity/ClassPSPACE/'
comps = {
 'ARM compiler + wide wrappers': [SC+'Machines/Compile', SC+'Machines/ARMWidth', SC+'Machines/ARMReach', SC+'Machines/ARMLoops', SC+'Machines/VWord'],
 'NARM': [SC+'Machines/NARM'],
 'MARM + time bridge': [SC+'Machines/MARM'],
 'Codec + deciders': [SC+'Codec/'],
 'InputAccess / PreimageHost': [SC+'Logspace/InputAccess', SC+'Logspace/PreimageHost'],
 'ExpBFS kit + ExpTime': [SC+'ExpBFS/', SC+'ExpTime'],
 'Savitch (SavitchARM)': [SC+'SavitchARM/'],
 'Inductive counting (ISCount*)': [SC+'Logspace/ISCount'],
 'PATH walk (PathWalk*)': [SC+'Logspace/PathWalk'],
 'PATH hardness (PathHard*)': [SC+'Logspace/PathHard'],
 'TQBF walk (TQBFARM)': [PS+'TQBFARM/'],
 'TQBF hardness (TQBFHard*)': [PS+'TQBFHard'],
}
def member(m, pref):
    return any(m == p or m.startswith(p) for p in pref)
for name, pref in comps.items():
    mods = sorted(m for m in g if member(m, pref))
    imp = sorted({m for m in g if not member(m, pref) and any(member(d, pref) for d in g[m])})
    print(f'## {name}: {len(mods)} modules')
    print('   modules:', ', '.join(x.replace('TCSlib/Complexity/', '') for x in mods))
    print('   direct importers outside:', ', '.join(x.replace('TCSlib/Complexity/', '') for x in imp) or '(none)')
