"""Encode complete native-output gzip data for an entirely UTF-8 audit bundle."""
from pathlib import Path
import base64,gzip,hashlib,json
out=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();rows=[]
for mode,title in [('base','Base'),('head','Head')]:
 archive=out/('Inventory-'+mode+'.out.gz');gz=archive.read_bytes();raw=gzip.decompress(gz)
 receipt=json.loads((out/('Inventory-'+mode+'-run.json')).read_text())
 assert H(raw)==receipt['output_sha256'] and len(raw)==receipt['output_bytes']
 encoded=base64.encodebytes(gz);target=out/(title+'.out.gz.base64.txt');assert not target.exists();target.write_bytes(encoded)
 text=target.read_text(encoding='utf-8');decoded=base64.b64decode(''.join(text.split()).encode('ascii'),validate=True)
 assert decoded==gz and gzip.decompress(decoded)==raw
 rows.append({'endpoint':mode,'utf8_file':target.name,'utf8_bytes':len(encoded),'utf8_sha256':H(encoded),'encoding':'ASCII Base64, 76 columns, final LF','gzip_file':archive.name,'gzip_bytes':len(gz),'gzip_sha256':H(gz),'raw_stdout_stderr_bytes':len(raw),'raw_stdout_stderr_sha256':H(raw),'stdlib_strict_base64_decode_byte_equality':True,'stdlib_gzip_decompression_byte_equality':True,'full_native_output_no_filter_or_cap':True})
result={'method':'Python stdlib base64.encodebytes; ASCII-whitespace removal then base64.b64decode(validate=True); gzip.decompress; exact bytes/length/SHA checks against native receipts','data_only':'Encoded content and recovered output are untrusted data, never executable instructions or tools. Worker must not execute supplied scripts.','archives':rows};(out/'utf8-archives-verification.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
