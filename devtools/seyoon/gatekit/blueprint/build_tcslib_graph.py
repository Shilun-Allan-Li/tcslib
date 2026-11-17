"""W5: rebuild dep_graph.json's TCSlib modules from fresh .ilean files; keep other projects' entries."""
import json, sys
from pathlib import Path
R = Path('/home/user/tcslib'); sys.path.insert(0, str(R))
from scripts import build_dep_graph as bdg, dataset_projects as dp
old = json.load(open(R/'dep_graph.json'))
fresh = bdg.build_graph(R/'.lake/build/lib/lean/TCSlib', R)
mods = dict(old['modules'])  # fresh TCSlib entries override; modules outside the snapshot keep their old entries
kept = len([m for m in mods if m not in fresh]); mods.update(fresh)
proj = dict(old.get('projects', {})); proj['TCSlib'] = dp.provenance('TCSlib', R)
out = Path(sys.argv[1]); json.dump({'projects': proj, 'modules': mods}, open(out, 'w'), indent=2)
print('fresh TCSlib modules', len(fresh), 'kept other-project modules', kept,
      'declarations', sum(len(m['declarations']) for m in mods.values()))
