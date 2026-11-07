"""Losslessly preserve every raw native output byte in deterministic gzip archives."""
from pathlib import Path
import gzip,hashlib,json
out=Path(__file__).resolve().parent;rows=[];H=lambda b:hashlib.sha256(b).hexdigest()
for mode in ['base','head']:
 rawpath=out/('Inventory-'+mode+'.out');gzpath=out/(rawpath.name+'.gz')
 data=rawpath.read_bytes();receipt=json.loads((out/('Inventory-'+mode+'-run.json')).read_text());assert H(data)==receipt['output_sha256'] and len(data)==receipt['output_bytes']
 assert not gzpath.exists();packed=gzip.compress(data,compresslevel=9,mtime=0);gzpath.write_bytes(packed)
 assert gzip.decompress(gzpath.read_bytes())==data
 rows.append({'mode':mode,'raw_filename':rawpath.name,'raw_bytes':len(data),'raw_sha256':H(data),'archive':gzpath.name,'archive_bytes':len(packed),'archive_sha256':H(packed),'decompression_byte_equality_verified':True})
 rawpath.unlink()
(out/'raw-log-archives.json').write_text(json.dumps({'raw_stdout_stderr_preserved_byte_for_byte':True,'format':'gzip, compression level9, mtime0','uncompressed_files_replaced_only_after_exact_decompression_check':True,'archives':rows},indent=2)+'\n');print(json.dumps(rows,indent=2))
