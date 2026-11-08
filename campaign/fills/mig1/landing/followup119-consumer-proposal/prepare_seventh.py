from pathlib import Path
import datetime,difflib,hashlib,json
p=Path(__file__).resolve().parent;H=lambda b:hashlib.sha256(b).hexdigest();baseline=(p/'inputs/Loop-baseline.lean.txt').read_text();start=baseline.index('private lemma emCall_eval_first ');end=baseline.index('\n/--',start)+1;old=baseline[start:end]
a=old.index('  have hex : ∃ t,');b=old.index('  have htag :',a)
newseg='''  obtain ⟨t, ht, hlive, heq⟩ :=
    MultiTapeTM.exists_first_halt M.tm (M.tm.initCfg s) hspec.1
  have hh : (M.tm.runFrom (M.tm.initCfg s) t).state = none := by
    rw [heq]
    exact hspec.1
  have hout : (M.tm.runFrom (M.tm.initCfg s) t).output = out := by
    rw [heq]
    exact hspec.2
'''
new=old[:a]+newseg+old[b:];assert old[:old.index(':= by')]==new[:new.index(':= by')]
(p/'inputs/Loop-emCall_eval_first-before.lean.txt').write_text(old);(p/'inputs/Loop-emCall_eval_first-after.lean.txt').write_text(new)
after=baseline[:start]+new+baseline[end:];(p/'seventh-existing-first-halt.patch').write_text(''.join(difflib.unified_diff(baseline.splitlines(keepends=True),after.splitlines(keepends=True),fromfile='a/TCSlib/Complexity/TuringMachine/Build/Loop.lean',tofile='b/TCSlib/Complexity/TuringMachine/Build/Loop.lean')))
six=(p/'inputs/Loop-after-b1-body-proposal-REQUIRES-API119.lean.txt').read_text();assert six.count(old)==1;seven=six.replace(old,new,1);(p/'inputs/Loop-after-b1-seven-body-proposal-REQUIRES-API119.lean.txt').write_text(seven)
receipt={'at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'Separate seventh mechanical proposal, authorized by parent under standing reuse rule; existing published NONE-first-halt API, not dependent on119 newtheorem.','declaration':'Turing.FinTM.emCall_eval_first [private]','baseline':'b1f553b315f31b949076e91119473ce4070e7d53','full_header_and_all_hypotheses_unchanged':True,'all_remaining_virtual_run_tag_return_cut_code_bytes_unchanged':True,'source_machine_endpoint':'Public exists_first_halt returns complete run(init s,t)=run(init s,T); hspec.1/2 transport halt and arbitrary out exactly','no_new_API_import_or_definition':True,'old_and_new_declaration_sha256':[H(old.encode()),H(new.encode())],'isolated_seventh_only_Loop_sha256':H(after.encode()),'combined_seven_body_Loop_sha256':H(seven.encode()),'native_execution':'NOT RUN for this production body; queued five generic/space leaves do not include it. No full speculative module/replay.','no_actual_source_changed':True};(p/'seventh-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
