"""Source-only exact marker comparison for two completed helper-check logs."""
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser(description=__doc__)
p.add_argument('--old',required=True);p.add_argument('--new',required=True);p.add_argument('--output',required=True)
a=p.parse_args();o=Path(a.output)
if o.exists():raise RuntimeError('refusing to overwrite evidence')
def read(path):
 raw=Path(path).read_bytes();lines=raw.decode().splitlines()
 if not lines or lines[-1]!='exit=0':raise RuntimeError('incomplete/nonpassing log: '+path)
 prefixes=('LAMP-CATALOG\t','LAMP-AXIOMS\t','LAMP-CLOSURE-EXACT\t','LAMP-INVENTORY-END\t')
 rows=[l for l in lines if l.startswith(prefixes)]
 return raw,rows,{pre[:-1]:sum(l.startswith(pre) for l in rows) for pre in prefixes}
b,br,bc=read(a.old);n,nr,nc=read(a.new)
result=dict(old=a.old,new=a.new,old_log_sha256=hashlib.sha256(b).hexdigest(),new_log_sha256=hashlib.sha256(n).hexdigest(),old_counts=bc,new_counts=nc,all_marker_rows_byte_exact=br==nr,all_marker_multisets_equal=sorted(br)==sorted(nr))
o.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
if not br==nr:raise SystemExit(1)
