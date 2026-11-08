from pathlib import Path
import hashlib,json,re,difflib,shutil
O=Path('/private/tmp/ab34-overnight-sg1-extras');P=Path('/private/tmp/ab34-overnight-sg1-harvest');R=Path('/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4')
def sha(b):return hashlib.sha256(b).hexdigest()
def chunk(s,n,kind='theorem'):
 m=re.search(r'(?m)^(?:private )?'+kind+' '+re.escape(n)+r'\b',s)
 if not m:raise ValueError(n)
 a=s.rfind('/--',0,m.start());ends=[i for p in ['\n/--','\n/-!','\nend ','\nnamespace '] if (i:=s.find(p,m.end()))>=0];return s[a:min(ends)].rstrip()
safe={
'SafeRun.zero':'''  have hs : Segment H {some avoid} (fun _ => True) c c 0 := Segment.zero True.intro
  have hp := (segment_iff H {some avoid} (fun _ => True) c c 0).mp hs
  exact ⟨hp.1, fun j hj hq => hp.2.1 j hj (Set.mem_singleton_iff.mpr hq)⟩''',
'SafeRun.cons':'''  have hs : Segment H {some avoid} (fun _ => True) c₁ c' t :=
    (segment_iff H {some avoid} (fun _ => True) c₁ c' t).mpr
      ⟨h.1, fun j hj hq => h.2 j hj (Set.mem_singleton_iff.mp hq), fun _ _ => True.intro⟩
  have hg := Segment.cons hstep
    (by simpa only [Set.mem_singleton_iff] using hc) True.intro hs
  have hp := (segment_iff H {some avoid} (fun _ => True) c c' (1 + t)).mp hg
  refine ⟨?_, ?_⟩
  · simpa only [Nat.add_comm 1 t] using hp.1
  · intro j hj hq
    exact hp.2.1 j (by omega) (Set.mem_singleton_iff.mpr hq)''',
'SafeRun.trans':'''  have hs₁ : Segment H {some avoid} (fun _ => True) c c₁ t₁ :=
    (segment_iff H {some avoid} (fun _ => True) c c₁ t₁).mpr
      ⟨h₁.1, fun j hj hq => h₁.2 j hj (Set.mem_singleton_iff.mp hq), fun _ _ => True.intro⟩
  have hs₂ : Segment H {some avoid} (fun _ => True) c₁ c' t₂ :=
    (segment_iff H {some avoid} (fun _ => True) c₁ c' t₂).mpr
      ⟨h₂.1, fun j hj hq => h₂.2 j hj (Set.mem_singleton_iff.mp hq), fun _ _ => True.intro⟩
  have hp := (segment_iff H {some avoid} (fun _ => True) c c' (t₁ + t₂)).mp
    (Segment.trans hs₁ hs₂)
  exact ⟨hp.1, fun j hj hq => hp.2.1 j hj (Set.mem_singleton_iff.mpr hq)⟩'''}
hard={
'clA5_pt_tail':'''  convert polyTimeComputable_tail using 1
  funext x
  cases x <;> rfl''',
'clA5_pt_head':'''  exact polyTimeComputable_take1'''}
mods={'TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean':safe,'TCSlib/Complexity/CookLevin/Hardness.lean':hard};rows=[];diff=[]
project=O/'native-project';(project/'.lake').mkdir(parents=True);(project/'.lake/packages').symlink_to(R/'.lake/packages',target_is_directory=True);shutil.copyfile(R/'lean-toolchain',project/'lean-toolchain')
for path,targets in mods.items():
 original=(R/path).read_text();assert original==(P/'source'/(path+'.txt')).read_text()
 current=original;combined=(P/'proposed-source'/(path+'.txt')).read_text();chunks=[]
 for n,body in targets.items():
  kind='lemma' if n.startswith('clA5_') else 'theorem';old=chunk(original,n,kind);prefix=old.split(':=',1)[0] if n=='SafeRun.zero' else old.split(':= by',1)[0];new=prefix+':= by\n'+body
  if n=='clA5_pt_tail':new=new.replace('/-- Removing the first bit is a two-state finite transduction. -/','/-- Removing the first bit is polynomial-time by the public tail closure. -/')
  if n=='clA5_pt_head':new=new.replace('/-- Extracting at most the first bit is also a two-state finite transduction. -/','/-- Extracting at most the first bit is polynomial-time by the public prefix closure. -/')
  assert old in current and old in combined;current=current.replace(old,new,1);combined=combined.replace(old,new,1)
  oldh=old[old.index('private lemma' if kind=='lemma' else 'theorem'):].split(':=',1)[0];newh=new[new.index('private lemma' if kind=='lemma' else 'theorem'):].split(':=',1)[0];assert oldh==newh
  rows.append({'path':path,'name':n,'original_source_sha256':sha(original.encode()),'old_chunk':old,'new_chunk':new,'old_chunk_sha256':sha(old.encode()),'new_chunk_sha256':sha(new.encode()),'full_header_sha256':sha(oldh.encode()),'header_exact':True,'no_new_import_or_public_API':True,'status':'native pending'});chunks.append(new)
 for category,s in [('source',original),('proposed-extra-source',current),('combined-native-source',combined)]:
  q=O/category/(path+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(s)
 diff+=difflib.unified_diff(original.splitlines(keepends=True),current.splitlines(keepends=True),fromfile='a/'+path,tofile='b/'+path)
 prints='\n\n'+'\n'.join('#print axioms '+('Turing.' if safe is targets else 'Complexity.')+n for n in targets)+'\n'
 q=project/path;q.parent.mkdir(parents=True,exist_ok=True);q.write_text(combined+prints);q=O/'probes'/(path+'.txt');q.parent.mkdir(parents=True,exist_ok=True);q.write_text(combined+prints)
 # Actual original imports, unmodified TCSlib import union; Lean support only for later metadata/control commands.
 imports='\n'.join(l for l in original.splitlines() if l.startswith('import '))+'\nimport Lean\n'
 scoped=imports+'set_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n'
 if safe is targets:
  scoped+='namespace Turing\nopen MultiTapeTM\nvariable {k m : ℕ} {B SS : Type} {x : List Bool}\n'+chunk(original,'SafeRun','def')+'\n'
 else:scoped+='namespace Complexity\nopen Turing\n'
 scoped+='\n'.join(chunks)+'\n'+prints+'\nend '+('Turing' if safe is targets else 'Complexity')+'\n'
 key='SafeRun' if safe is targets else 'HardnessLeaves'
 (O/(key+'-scope-native.lean.txt')).write_text(scoped);(project/(key+'ScopeNative.lean')).write_text(scoped)
(O/'extras-only.patch').write_text(''.join(diff));(O/'chunk-mappings.json').write_text(json.dumps(rows,indent=2,ensure_ascii=False)+'\n')
(O/'scope.json').write_text(json.dumps({'source':'9b5dcf46408db681bcbc721930ef2203fa6bc47d','base8_tranche_manifest':'ff454846e5f1da35105d333b9f7905a12145613a580435811e122cbceabf3784','extra_roots':5,'no_API_import_name_statement_definition_changes':True,'combined_native_probes':'Extras plus earlier authorized same-owner mechanical roots; extra patch itself contains only5 new roots.','seals_controls_pending':True},indent=2)+'\n')
print('Prepared extra-only5-root patch and combined native owner probes; imports and headers exact.')
