"""Create and verify a ZIP with seq-zk/ root and exact ordinary-file/hash coverage."""
from pathlib import Path
import sys,zipfile,hashlib,json
root=Path(sys.argv[1]);out=Path(sys.argv[2]);assert root.name=='seq-zk' and not out.exists()
files=sorted(p for p in root.rglob('*') if p.is_file());assert not any(p.is_symlink() for p in root.rglob('*'))
with zipfile.ZipFile(out,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=6,allowZip64=True) as z:
 z.write(root,'seq-zk/')
 for p in files:z.write(p,'seq-zk/'+p.relative_to(root).as_posix())
with zipfile.ZipFile(out) as z:
 assert z.testzip() is None
 entries=[n for n in z.namelist() if not n.endswith('/')];assert len(entries)==len(set(entries))==len(files)
 assert set(entries)=={'seq-zk/'+p.relative_to(root).as_posix() for p in files}
 for p in files:assert hashlib.sha256(z.read('seq-zk/'+p.relative_to(root).as_posix())).digest()==hashlib.sha256(p.read_bytes()).digest(),p
metadata=dict(zip=str(out),bytes=out.stat().st_size,sha256=hashlib.sha256(out.read_bytes()).hexdigest(),root='seq-zk/',files=len(files),uncompressed_bytes=sum(p.stat().st_size for p in files),all_entries_and_SHA256_verified=True,payload_top_manifest_sha256=hashlib.sha256((root/'SHA256SUMS').read_bytes()).hexdigest())
out.with_suffix('.json').write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata,indent=2))
