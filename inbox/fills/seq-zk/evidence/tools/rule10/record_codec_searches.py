"""Record base-tree searches and helper promotion requests; no Lean execution."""
import datetime
import json
from pathlib import Path
import subprocess

repo = Path('/private/tmp/hash-sign-fill/repo')
base = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
out = Path(__file__).resolve().parents[2] / 'rule10' / 'codec-searches.json'
rows = []
for pattern in [r'MachineCodec\.ext|theorem.*[Cc]odec.*ext|theorem.*ext.*[Cc]odec|forgerCodec_eq',
                r'splitBits.*append|splitBits.*concat|Fin\.append.*splitBits']:
    cmd = ['git', '--no-optional-locks', '-C', str(repo), 'grep', '-n', '-E', pattern, base, '--', 'TCSlib']
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
    rows.append({'command': cmd, 'exit': p.returncode, 'output': p.stdout})
record = {'base': base, 'recorded_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'searches': rows, 'conclusion': 'No relevant existing codec extensionality, complete forger-codec reader, or split/concatenation lemma found.',
          'promotions': [
             {'declaration': 'Games.MachineCodec.ext_of_fields', 'destination': 'Games/Machines.lean'},
             {'declaration': 'Authentication.SignatureScheme.forgerCodec_eq_bitCodec', 'destination': 'Authentication/Signatures/Defs.lean'},
             {'declaration': 'Authentication.HashSignFill.splitBits_append', 'destination': 'Authentication/Encoding.lean'},
             {'declaration': 'Authentication.HashSignFill.splitBits_pad_concat', 'destination': 'Authentication/Encoding.lean'}],
          'overlap': 'None: the only text matches are unrelated TQBF codec_symbol_ext and Efficiency.Handler advNext_eq.'}
out.parent.mkdir(parents=True, exist_ok=True)
out.write_text(json.dumps(record, indent=2) + '\n')
print(str(out))
