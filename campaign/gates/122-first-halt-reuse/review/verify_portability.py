from pathlib import Path,PurePosixPath
import argparse,json,hashlib,shutil
ap=argparse.ArgumentParser();ap.add_argument('--root',default=str(Path(__file__).resolve().parent));ap.add_argument('--reconstruct',action='store_true');ap.add_argument('--allow-preparing',action='store_true');a=ap.parse_args();R=Path(a.root).resolve();H=lambda b:hashlib.sha256(b).hexdigest()
def path(rel):
 p=PurePosixPath(rel);assert not p.is_absolute() and '..' not in p.parts and '\n' not in rel and '\r' not in rel,rel
 q=R/str(p);q.resolve().relative_to(R);return q
u=json.loads(path('BUNDLE-UNIVERSE.json').read_text());m=json.loads(path('BUNDLE-OMISSION-RECOVERY.json').read_text());assert u['core_file_count']==len(u['files']);rows={r['path']:r for r in u['files']};assert len(rows)==len(u['files']);om={r['omitted_path']:r for r in m['omissions']};selected=path('BUNDLE-FILES.portable.txt').read_text().splitlines();assert len(selected)==len(set(selected));chosen=set(selected);assert set(om)=={p for p,r in rows.items() if r['disposition']=='EXACT_HISTORICAL_DUPLICATE'};assert all(p.startswith('inputs/historical-fh10-e0b/') for p in om)
checked=restored=0
for rel,r in rows.items():
 q=path(rel)
 if rel in om:
  d=om[rel];target=d['recover_from_retained_path'];assert target in rows and target in chosen and target not in om;tr=rows[target];assert d['sha256']==r['sha256']==tr['sha256'] and d['bytes']==r['bytes']==tr['bytes'];b=path(target).read_bytes();assert H(b)==r['sha256'] and len(b)==r['bytes']
  if q.exists():assert q.read_bytes()==b,rel
  elif a.reconstruct:q.parent.mkdir(parents=True,exist_ok=True);q.write_bytes(b);restored+=1
 else:
  assert rel in chosen,rel;b=q.read_bytes();assert H(b)==r['sha256'] and len(b)==r['bytes'],rel
 if q.exists():assert H(q.read_bytes())==r['sha256'] and q.stat().st_size==r['bytes'],rel
 checked+=1
meta=set(u['retained_metadata_files']);integrity=set(u['retained_final_integrity_files']);assert chosen=={p for p,r in rows.items() if r['disposition']=='RETAINED'}|meta|integrity
actual_paths={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file()};assert not actual_paths-(set(rows)|meta|integrity),sorted(actual_paths-(set(rows)|meta|integrity))
missing=[p for p in selected if not path(p).is_file()];assert not missing or a.allow_preparing and set(missing)<=integrity,missing
# The final full-record manifest preserves every logical payload, including omitted copies.
manifest=path('MANIFEST.json')
if manifest.exists():
 mm=json.loads(manifest.read_text());mr={r['path']:r for r in mm['files']}
 for rel,r in rows.items():assert rel in mr and mr[rel]['sha256']==r['sha256'] and mr[rel]['bytes']==r['bytes'],rel
 for rel in meta:
  b=path(rel).read_bytes();assert mr[rel]['sha256']==H(b) and mr[rel]['bytes']==len(b),rel
actual=[p for p in selected if path(p).is_file()];size=sum(path(p).stat().st_size for p in actual)
print(json.dumps({'verified_core_logical_files':checked,'omitted_historical_exact_duplicates':len(om),'one_hop_recoveries_all_to_retained_files':True,'restored_files':restored,'selected_files':len(selected),'selected_files_present':len(actual),'selected_bytes_present':size,'missing_only_preparing_integrity_files':missing,'under_90_decimal_MB_before_root_supplements':size<90000000,'full_record_manifest_checked':manifest.exists(),'no_Lean_screen_Git_or_source_worktree_action':True},indent=2))
