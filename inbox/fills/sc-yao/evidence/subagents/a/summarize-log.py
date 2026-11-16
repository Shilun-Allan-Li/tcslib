from pathlib import Path
import json
import re
import sys
module, name, status = sys.argv[1:]
s = Path(name).read_text()
result = {
    'module': module,
    'log': name,
    'status': int(status),
    'errors': len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', s, re.M)),
    'sorry_warnings': len(re.findall("declaration uses 'sorry'", s)),
    'warnings': len(re.findall(r'^\S+\.lean:\d+:\d+: warning:', s, re.M)),
}
with Path('evidence/subagents/a/results.jsonl').open('a') as f:
    f.write(json.dumps(result) + '\n')
print(json.dumps(result))
