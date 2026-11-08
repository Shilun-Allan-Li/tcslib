"""Build/verify one source-byte-preserving common-evidence ZIP from a full records commit."""
from pathlib import Path,PurePosixPath
import hashlib,json,subprocess,sys,tarfile,zipfile
ROOT=Path.cwd();PREFIX='briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/'

def need(ok,message):
 if not ok:raise RuntimeError(message)

def main():
 rev=sys.argv[1];out=Path(sys.argv[2]).resolve()
 need(len(rev)==40 and subprocess.check_output(['git','rev-parse',rev+'^{commit}'],text=True).strip()==rev,'full records commit required')
 need(out.is_relative_to((ROOT/'.lake/ps-maintainer/gate06').resolve()) and not out.exists(),'fresh ignored output required')
 names=subprocess.check_output(['git','ls-tree','-r','-z','--name-only',rev,'--',PREFIX]).decode().split('\0')[:-1]
 need(names and all(n.startswith(PREFIX) and '..' not in PurePosixPath(n).parts for n in names),'unexpected archive path')
 need(not any(Path(n).suffix in {'.pdf','.olean','.ilean'} for n in names),'books/caches must not enter evidence archive')
 manifest_name=PREFIX+'FINAL-EVIDENCE-FILES.sha256'
 raw_manifest=subprocess.check_output(['git','show',rev+':'+manifest_name],text=True)
 expected={}
 for line in raw_manifest.splitlines():
  if not line or line.startswith('#'):continue
  digest,name=line.split('  ',1);need(name not in expected and len(digest)==64,'bad file manifest');expected[name]=digest
 need(set(expected)==set(names)-{manifest_name},'raw file manifest does not equal records archive set')
 out.mkdir();archive=out/'gate06-common-evidence.zip';actual={};sizes={}
 proc=subprocess.Popen(['git','archive','--format=tar',rev,'--',PREFIX],stdout=subprocess.PIPE)
 with tarfile.open(fileobj=proc.stdout,mode='r|') as stream,zipfile.ZipFile(archive,'x',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as target:
  for member in stream:
   if member.isdir():continue
   need(member.isfile() and member.name in names,'nonordinary/unexpected archive member')
   source=stream.extractfile(member);need(source is not None,'missing tar member')
   info=zipfile.ZipInfo(member.name,date_time=(1980,1,1,0,0,0));info.compress_type=zipfile.ZIP_DEFLATED;info.external_attr=0o100644<<16
   digest=hashlib.sha256();size=0
   with target.open(info,'w') as dest:
    while chunk:=source.read(1<<20):dest.write(chunk);digest.update(chunk);size+=len(chunk)
   actual[member.name]=digest.hexdigest();sizes[member.name]=size
 need(proc.wait()==0 and set(actual)==set(names),'Git archive incomplete')
 need(all(actual[n]==h for n,h in expected.items()),'raw artifact SHA differs from committed final manifest')
 with zipfile.ZipFile(archive) as check:
  need(len(check.namelist())==len(names) and set(check.namelist())==set(names),'ZIP duplicate/missing member')
  for name in names:need(hashlib.sha256(check.read(name)).hexdigest()==actual[name],'ZIP roundtrip mismatch')
 need(archive.stat().st_size<90_000_000,'common ZIP exceeds chosen Git transport bound')
 (out/'ZIP-CONTENTS.tsv').write_text('revision\tpath\tbytes\tsha256\n'+''.join(f'{rev}\t{n}\t{sizes[n]}\t{actual[n]}\n' for n in sorted(names)))
 data={'records_commit':rev,'archive':'gate06-common-evidence.zip','archive_sha256':hashlib.sha256(archive.read_bytes()).hexdigest(),'archive_bytes':archive.stat().st_size,'artifact_count':len(names),'uncompressed_bytes':sum(sizes.values()),'all_Git_bytes_and_ZIP_roundtrip_verified':True,'file_manifest_path':manifest_name,'file_manifest_sha256':actual[manifest_name],'builder_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'books_or_oleans_included':False}
 (out/'manifest.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data),flush=True)

if __name__=='__main__':main()
