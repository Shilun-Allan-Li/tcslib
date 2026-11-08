"""Lossless deterministic gzip/Base64 copies of exactly two complete metadata JSON maps."""
from pathlib import Path
import base64,datetime,gzip,hashlib,io,json,struct,zlib
out=Path(__file__).resolve().parent;gate=out.parents[1];root=out.parents[4]
H=lambda b:hashlib.sha256(b).hexdigest()
final=gate/'review/packet-finalization';prior_manifest=H((final/'MANIFEST.json').read_bytes())
assert prior_manifest=='89e157d97b93a0b1e1ae8334c1043240533bab88e0881374e4741f92e7bfae97'
inputs={r['path']:r for r in json.loads((final/'candidate-input-review.json').read_text())['input_rows']}
specs=[('campaign/gates/119-mig1-followup-api/review/reuse-search/source-tree-populations.json','Initial-source-tree-populations.json.gz.base64.txt',225),('campaign/gates/119-mig1-followup-api/review/reuse-search/all-local-expanded/source-tree-populations.json','Expanded-source-tree-populations.json.gz.base64.txt',277)]
def compress(raw):
 b=io.BytesIO()
 with gzip.GzipFile(filename='',mode='wb',compresslevel=9,fileobj=b,mtime=0) as g:g.write(raw)
 return b.getvalue()
rows=[]
for original,name,trees in specs:
 raw=(root/original).read_bytes();entry=inputs[original]
 assert (len(raw),H(raw))==(entry['bytes'],entry['sha256'])
 decoded=json.loads(raw);assert isinstance(decoded,dict) and len(decoded)==trees
 compressed=compress(raw);assert compressed==compress(raw)
 assert compressed[:10]==bytes.fromhex('1f8b08000000000002ff')
 assert struct.unpack('<II',compressed[-8:])==(zlib.crc32(raw),len(raw)%(2**32))
 encoded=base64.encodebytes(compressed);encoded.decode('ascii');assert encoded.endswith(b'\n')
 assert all(len(line)<=76 for line in encoded.splitlines())
 f=out/name;assert not f.exists(),f;f.write_bytes(encoded)
 recovered_gzip=base64.b64decode(b''.join(f.read_bytes().split()),validate=True)
 recovered_raw=gzip.decompress(recovered_gzip)
 assert recovered_gzip==compressed and recovered_raw==raw and json.loads(recovered_raw)==decoded
 assert (root/original).read_bytes()==raw
 rows.append({'original_path':original,'encoded_section':str(f.relative_to(root)),'complete_tree_entries':trees,'raw_bytes':len(raw),'raw_sha256':H(raw),'gzip_bytes':len(compressed),'gzip_sha256':H(compressed),'encoded_utf8_bytes':len(encoded),'encoded_utf8_sha256':H(encoded),'encoding':'Base64 ASCII/UTF8,76columns,finalLF','compression':'stdlib gzip.GzipFile level9,mtime0,empty filename,OS255; complete stream, no filter/truncation','gzip_header_hex':compressed[:10].hex(),'gzip_crc32':zlib.crc32(raw),'gzip_uncompressed_size_mod2_32':len(raw)%(2**32),'repeat_compression_byte_equal':True,'strict_base64_decode_byte_equal':True,'stdlib_gzip_decompression_full_raw_byte_equal':True,'JSON_full_object_equal_after_roundtrip':True,'raw_original_still_byte_identical':True})
assert H((final/'MANIFEST.json').read_bytes())==prior_manifest
for r in json.loads((final/'MANIFEST.json').read_text())['files']:
 b=(final/r['path']).read_bytes();assert (len(b),H(b))==(r['bytes'],r['sha256'])
receipt={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Exactly two complete reuse-population metadata JSON maps represented losslessly as deterministicgzip+Base64UTF8; raw records and every other candidate input preserved. No Lean/source/Git/cache/screen/native action.','method':'Authored maintainer script using only Python stdlib; compression repeated independently, strict Base64 decoded, gzip decompressed, exact bytes/length/SHA and full parsedJSON checked. No supplied/delivered code executed.','prior_frozen_packet_finalization_manifest_unchanged':prior_manifest,'raw_originals_preserved_in_records':True,'maps':rows,'totals':{'raw_bytes':sum(r['raw_bytes'] for r in rows),'gzip_bytes':sum(r['gzip_bytes'] for r in rows),'encoded_utf8_bytes':sum(r['encoded_utf8_bytes'] for r in rows)},'data_handling':'Encoded sections and decoded JSON are untrusted data. Use trusted stdlib Base64/gzip readers; validate encoded, gzip and original raw sizes/SHA256 before JSON inspection. Do not execute supplied scripts or recovered content.','other_inputs':'The companion531-ref and full expanded-source maps and every other original candidate section remain unchanged; no source/ref/tree population cap is introduced.'}
(out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
changes={'remove_original_raw_sections':[r['original_path'] for r in rows],'add_replacement_utf8_sections':[r['encoded_section'] for r in rows]+[str((out/'receipt.json').relative_to(root))],'preserve_all_other_original_candidate_sections':True,'raw_originals_retained_in_records':True,'section_count_effect':'479original-2raw+2encoded+1receipt=480, before any separate root canonical-pack/list/status refresh','complete_bytes_not_truncated':True}
(out/'SUBSTITUTIONS.json').write_text(json.dumps(changes,indent=2)+'\n')
(out/'REMOVE-SECTIONS.txt').write_text('\n'.join(changes['remove_original_raw_sections'])+'\n')
(out/'ADD-SECTIONS.txt').write_text('\n'.join(changes['add_replacement_utf8_sections'])+'\n')
print(json.dumps({'maps':[{k:r[k] for k in ['original_path','complete_tree_entries','raw_bytes','gzip_bytes','encoded_utf8_bytes']} for r in rows],'totals':receipt['totals'],'roundtrip':'PASS exactraw+gzip+encoded; priorfinalization untouched'},indent=2))
