from pathlib import Path
import sys,json,hashlib
root=Path(sys.argv[1]);rows=[]
for name in sys.argv[2:]:
 raw=(root/name).read_bytes();text=raw.decode();rows.append({'path':name,'bytes':len(raw),'lines_splitlines':len(text.splitlines()),'lines_style_lint_split_newline':len(text.split('\n')),'newline_count':raw.count(b'\n'),'sha256':hashlib.sha256(raw).hexdigest(),'over1000_splitlines':len(text.splitlines())>1000,'over600_splitlines':len(text.splitlines())>600})
print(json.dumps(rows,indent=2))
