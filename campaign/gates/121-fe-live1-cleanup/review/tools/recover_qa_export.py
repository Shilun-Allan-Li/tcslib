from pathlib import Path, PurePosixPath
import sys,json,base64,gzip,tarfile,io,hashlib
B=Path(__file__).resolve().parents[1];phase=sys.argv[1];assert phase in ['BASE','HEAD'];dest=Path(sys.argv[2]).resolve();assert not dest.exists()
index=json.loads((B/'qa/encoded-exports/ARCHIVE-MEMBERS.json').read_text());row=next(r for r in index['archives']if r['phase']==phase)
encoded=(B/row['encoded_file']).read_bytes();assert hashlib.sha256(encoded).hexdigest()==row['encoded_SHA256'];compressed=base64.decodebytes(encoded);assert hashlib.sha256(compressed).hexdigest()==row['gzip_SHA256'];raw=gzip.decompress(compressed);assert hashlib.sha256(raw).hexdigest()==row['tar_SHA256']
dest.mkdir(parents=True)
with tarfile.open(fileobj=io.BytesIO(raw),mode='r:')as tar:
 members=tar.getmembers();assert len(members)==row['member_count']
 for m,want in zip(members,row['members']):
  p=PurePosixPath(m.name);assert m.isfile()and not p.is_absolute()and '..'not in p.parts and m.name==want['path']
  data=tar.extractfile(m).read();data.decode('utf-8');assert len(data)==want['bytes']and hashlib.sha256(data).hexdigest()==want['SHA256'];out=dest.joinpath(*p.parts);out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(data)
print(json.dumps({'phase':phase,'recovered_members':len(members),'destination':str(dest),'SHA256_all_exact':True}))
