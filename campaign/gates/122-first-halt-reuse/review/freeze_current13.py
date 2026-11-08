from pathlib import Path
import json,hashlib,shutil,subprocess,sys
O=Path(__file__).parent;D=Path('/private/tmp/ab34-fh13-screen44');H=lambda b:hashlib.sha256(b).hexdigest();complete=json.loads((D/'COMPLETE.json').read_text());assert complete['pass'] and complete['head']=='f3c8c050ef98375bc237c72bde74f83d33833374' and complete['population']==44
reviews=json.loads((O/'screen/pair-dispositions.json').read_text());delta=json.loads((O/'screen/pair-delta.json').read_text());assert len(reviews)==len(delta['new'])+len(delta['BASE_only'])+len(delta['persistent_score_changed']);assert all(r['source_review_complete'] and r['no_new_fix_required'] for r in reviews)
assert json.loads((O/'STATUS.json').read_text())['state']=='COMPLETE_PRIVATE_EVIDENCE_ROOT_PUBLICATION_PENDING'
for p in O.rglob('*'):
 assert not p.is_symlink()
 if p.is_file():assert p.suffix not in ['.lean','.olean','.ilean','.pdf','.pyc'];p.read_bytes().decode('utf-8')
# The full physical record stays intact. The transport list is only exact historical byte deduplication.
r=subprocess.run(['python3','-I',str(O/'prepare_portability.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
F=Path('/private/tmp/ab34-gate122-fh13-frozen');assert not F.exists();shutil.copytree(O,F)
files=[{'path':str(p.relative_to(F)),'bytes':p.stat().st_size,'sha256':H(p.read_bytes())} for p in sorted(F.rglob('*')) if p.is_file() and str(p.relative_to(F)) not in ['MANIFEST.json','SHA256SUMS']]
(F/'MANIFEST.json').write_text(json.dumps({'payload_count':len(files),'payload_bytes':sum(r['bytes'] for r in files),'source_HEAD':'f3c8c050ef98375bc237c72bde74f83d33833374','BASE':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','actual_selected_complete_roots':13,'actual_changed_owners':8,'actual_current_tail_modules':153,'historical_previous_modules':222,'actual_screen_population':44,'files':files,'self_and_SHA256SUMS_excluded':True,'publication_scope':'complete private evidence; root owns canonical pack/helper11/records/exchange/dispatch/gate closure'},indent=2)+'\n');(F/'SHA256SUMS').write_text(''.join(r['sha256']+'  '+r['path']+'\n' for r in files))
for r in files:assert H((F/r['path']).read_bytes())==r['sha256']
check=subprocess.run(['python3','-I',str(F/'verify_portability.py'),'--root',str(F)],capture_output=True,text=True);assert check.returncode==0,check.stderr;print(check.stdout)
selected=(F/'BUNDLE-FILES.portable.txt').read_text().splitlines();selected_bytes=sum((F/p).stat().st_size for p in selected);assert selected_bytes<90000000
print(json.dumps({'frozen':str(F),'payload_count':len(files),'full_record_payload_bytes':sum(r['bytes'] for r in files),'MANIFEST_sha256':H((F/'MANIFEST.json').read_bytes()),'REVIEW_sha256':H((F/'FINAL-REVIEW.md').read_bytes()),'portable_selected_files':len(selected),'portable_file_bytes_before_root_supplements':selected_bytes,'all_files_physically_preserved':True},indent=2))
