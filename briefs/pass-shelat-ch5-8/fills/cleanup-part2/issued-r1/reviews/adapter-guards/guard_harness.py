"""Own non-native guard simulation. The only adapter target captures argv as JSON."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT=Path(__file__).resolve().parent
PREP=ROOT.parent
TOOLS=PREP/'external-tools-r1'
STATIC=PREP/'external-bootstrap-r1'
CLONE=Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
PINS={'prepare_pfr.py':'650edf1d270d5e130a926a5840fead75ba9888e12684f2f38451af91ad769b8f',
      'pfr_lean.py':'41fda9565be3f77462fe6f2f7b55b798c5bf34fbbc400a648f77e000eb36636d'}


def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_json(path,value):
    with Path(path).open('x') as f:json.dump(value,f,indent=2);f.write('\n')


def pin_tools():
    for name,h in PINS.items():assert sha(TOOLS/name)==h,('portable tool changed',name)


def main():
    pin_tools()
    assert not (ROOT/'cases').exists(),'Fresh exclusive case directory required'
    cases=ROOT/'cases';cases.mkdir()
    fake=ROOT/'capture_only'
    fake.write_text('#!'+sys.executable+' -I\n'+
      'import json, os, sys\nfrom pathlib import Path\n'+
      'p=Path(os.environ["PFR_GUARD_CAPTURE"]).resolve()\n'+
      'assert p.is_relative_to(Path('+repr(str(ROOT))+').resolve()) and p.suffix == ".json"\n'+
      'with p.open("x") as f: json.dump({"argv":sys.argv,"cwd":os.getcwd(),"python":sys.executable},f,indent=2)\n'+
      'print("ARGV_CAPTURE_ONLY_NO_LEAN_NO_OBJECT")\n')
    fake.chmod(0o755)
    fake_hash=sha(fake)
    results=[]
    static_before={str(p):sha(p) for p in STATIC.iterdir() if p.is_file()}
    source_metadata={str(CLONE/'lean-toolchain'):sha(CLONE/'lean-toolchain'),
                     str(CLONE/'lake-manifest.json'):sha(CLONE/'lake-manifest.json')}
    for row in json.loads((STATIC/'ordered-modules.json').read_text()):source_metadata[row['source_path']]=sha(row['source_path'])
    source_metadata[str(CLONE/'.lake/packages/PFR/lakefile.toml')]=sha(CLONE/'.lake/packages/PFR/lakefile.toml')

    def case(name):
        p=cases/name;p.mkdir();return p

    def run(name,argv,cwd,*,cfg=None,expected_rc_zero=False,guard=None,notes=''):
        pin_tools()
        folder=cases/name
        capture=folder/'capture.argv.json'
        env=os.environ.copy();env['PFR_GUARD_CAPTURE']=str(capture)
        if cfg:env['PFR_BOOTSTRAP_CONFIG']=str(cfg)
        before_cfg=sha(cfg) if cfg else None
        proc=subprocess.run([str(x) for x in argv],cwd=str(cwd),env=env,
                            stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=30)
        (folder/'stdout.txt').write_bytes(proc.stdout);(folder/'stderr.txt').write_bytes(proc.stderr)
        success=(proc.returncode==0)==expected_rc_zero
        if guard:success=success and guard.encode() in proc.stderr
        row={'case':name,'argv':[str(x) for x in argv],'cwd':str(cwd),'rc':proc.returncode,
             'expected_rc_zero':expected_rc_zero,'expected_guard_fragment':guard,
             'expectation_met':success,'capture_exists':capture.exists(),
             'config_sha256_before':before_cfg,'config_sha256_after':sha(cfg) if cfg else None,
             'stdout_sha256':sha(folder/'stdout.txt'),'stderr_sha256':sha(folder/'stderr.txt'),
             'portable_tool_sha256':PINS.copy(),'notes':notes}
        if capture.exists():row['capture_sha256']=sha(capture);row['capture']=json.loads(capture.read_text())
        write_json(folder/'result.json',row);results.append(row);return row

    def prepare(name,setup=None,supplement=STATIC,expected=False,guard=None,notes=''):
        folder=case(name);tree=folder/'tree';runtime=folder/'runtime'
        if setup:setup(folder,tree,runtime)
        row=run(name,[sys.executable,'-I',TOOLS/'prepare_pfr.py',CLONE,tree,supplement,runtime,fake],
                ROOT,expected_rc_zero=expected,guard=guard,notes=notes)
        row['runtime_exists']=runtime.exists();row['tree_exists']=tree.exists()
        row['no_captured_target_during_prepare']=not (folder/'capture.argv.json').exists()
        write_json(folder/'post-state.json',{'runtime_exists':runtime.exists(),'tree_exists':tree.exists(),
                   'all_paths':sorted(str(p.relative_to(folder)) for p in folder.rglob('*'))})
        return folder,tree,runtime,row

    base,tree,runtime,prep_result=prepare('P01_allowed_prepare',expected=True)
    assert prep_result['expectation_met'] and not prep_result['capture_exists']
    cfg0=json.loads((runtime/'config.json').read_text());entry=runtime/'bin/lean'
    assert cfg0['real_lean']==str(fake) and cfg0['real_lean_sha256']==fake_hash
    relative=next(iter(cfg0['sources']))
    output=tree/(relative.removesuffix('.lean')+'.olean')
    assert not output.exists()

    prepare('P02_existing_runtime',lambda f,t,r:r.mkdir(),guard='Use a fresh runtime directory')
    prepare('P03_conflicting_logical_directory',lambda f,t,r:(t.mkdir(),(t/'PFR').mkdir()),guard='Conflicting PFR object prefix')
    def logical_wrong(f,t,r):
        t.mkdir();other=f/'other';other.mkdir();(t/'PFR').symlink_to(other,target_is_directory=True)
    prepare('P04_conflicting_logical_symlink',logical_wrong,guard='Conflicting PFR object prefix')
    def physical_escape(f,t,r):
        t.mkdir();outside=f/'outside';outside.mkdir();(outside/'sentinel.txt').write_text('unchanged\n')
        (t/'.lake').symlink_to(outside,target_is_directory=True)
    f,t,r,row=prepare('P05_physical_prefix_escape',physical_escape,guard='Physical object prefix escapes the one tree')
    assert sorted(x.name for x in (f/'outside').iterdir())==['sentinel.txt']
    assert not r.exists()
    row['outside_unchanged_before_mkdir']=True

    def static_copy(name,mutate,update_delivery=False):
        folder=case(name);target=folder/'static-data';target.mkdir()
        for source in STATIC.iterdir():
            if source.is_file():(target/source.name).write_bytes(source.read_bytes())
        mutate(target)
        if update_delivery:
            d=json.loads((target/'DELIVERY-MANIFEST.json').read_text())
            for item in d['files']:
                f=target/item['path'];item['bytes']=f.stat().st_size;item['sha256']=sha(f)
            (target/'DELIVERY-MANIFEST.json').write_text(json.dumps(d,indent=2)+'\n')
        run(name,[sys.executable,'-I',TOOLS/'prepare_pfr.py',CLONE,folder/'tree',target,folder/'runtime',fake],ROOT,
            guard='Frozen PFR inventory manifest drift' if update_delivery else 'Frozen PFR inventory data drift',
            notes='Modified own metadata copies only; outer frozen-manifest integrity rejects before package processing.')
        assert not (folder/'tree').exists() and not (folder/'runtime').exists()

    def edit_rows(target,fn):
        f=target/'ordered-modules.json';rows=json.loads(f.read_text());fn(rows);f.write_text(json.dumps(rows,indent=2)+'\n')
    def duplicate(rows):
        rows[1]={**rows[0],'ordinal':2}
    static_copy('P06_duplicate_module_metadata',lambda p:edit_rows(p,duplicate))
    static_copy('P07_module_path_metadata',lambda p:edit_rows(p,lambda r:r[0].update(package_relative_source='PFR/Unlisted.lean')))
    def reorder(target,strip=False):
        f=target/'ordered-modules.json';rows=json.loads(f.read_text());rows[0],rows[1]=rows[1],rows[0]
        for i,r in enumerate(rows,1):
            r['ordinal']=i
            if strip:r['imports']=[]
        f.write_text(json.dumps(rows,indent=2)+'\n')
        (target/'bootstrap-order.txt').write_text(''.join('.lake/packages/PFR/'+r['package_relative_source'].removesuffix('.lean')+'\n' for r in rows))
    static_copy('P08_wrong_dependency_order',reorder)
    static_copy('P09_order_file_tamper',lambda p:(p/'bootstrap-order.txt').write_text('wrong\n'))
    static_copy('P10_coordinated_order_import_manifest_tamper',lambda p:reorder(p,True),update_delivery=True)

    def driver(name,change=None,args=None,cwd=CLONE,tool=None,expect=False,guard=None,notes=''):
        folder=case(name);cfg=json.loads(json.dumps(cfg0))
        if change:change(cfg,folder)
        assert Path(cfg['real_lean']).resolve().is_relative_to(ROOT),'Target must always be own harmless executable'
        cfgpath=folder/'config.json';write_json(cfgpath,cfg)
        argv=[entry,*([relative,'-o',str(output)] if args is None else args)] if tool is None else [sys.executable,'-I',tool,relative,'-o',str(output)]
        row=run(name,argv,cwd,cfg=cfgpath,expected_rc_zero=expect,guard=guard,notes=notes)
        if not expect:assert not row['capture_exists'],('Rejected call reached fake target',name)
        return row

    allowed=driver('D01_allowed_exact_invocation',expect=True)
    expected=[str(fake),'--root='+str(CLONE/'.lake/packages/PFR'),
              '-DautoImplicit=false','-DrelaxedAutoImplicit=false','-Dpp.unicode.fun=true','-Dpp.proofs.withType=false',relative,'-o',str(output)]
    assert allowed['capture']['argv']==expected and allowed['capture']['cwd']==str(CLONE)
    assert not output.exists()
    nonlisted=next(p for p in sorted((CLONE/'.lake/packages/PFR/PFR').rglob('*.lean'))
                   if str(p.relative_to(CLONE)) not in cfg0['sources'])
    driver('D02_nonlisted_existing_source',args=[str(nonlisted.relative_to(CLONE)),'-o',str(output)],guard='Source is outside the fixed PFR closure')
    driver('D03_extra_argument',args=[relative,'-o',str(output),'--trust=1'],guard='Unexpected checker argument shape')
    driver('D04_wrong_cwd',cwd=ROOT)
    driver('D05_object_outside_tree',args=[relative,'-o',str(ROOT/'not-an-object.olean')],guard='Object escapes the one tree')
    driver('D06_wrong_object_inside_tree',args=[relative,'-o',str(tree/'wrong.olean')],guard='Object escapes the one tree')
    driver('D07_source_hash_config_drift',change=lambda c,f:c['sources'][relative].update(sha256='0'*64),guard='Pinned PFR source drift',notes='Expected source hash changed in own config; package source never edited.')
    driver('D08_lakefile_hash_config_drift',change=lambda c,f:c.update(pfr_lakefile_sha256='0'*64))
    driver('D09_driver_hash_config_drift',change=lambda c,f:c.update(driver_sha256='0'*64),guard='Adapter source drift')
    driver('D10_real_binary_hash_config_drift',change=lambda c,f:c.update(real_lean_sha256='0'*64))
    def actual_binary_drift(c,f):
        other=f/'capture_only_drifted';other.write_bytes(fake.read_bytes()+b'\n# own drift simulation\n');other.chmod(0o755)
        c['real_lean']=str(other) # Keep the original prepared byte hash.
    driver('D11_actual_real_binary_drift',change=actual_binary_drift)
    shadow=ROOT/'own_driver_drift_simulation.py'
    shadow.write_bytes((TOOLS/'pfr_lean.py').read_bytes()+b'\n# own scratch-copy drift simulation\n')
    driver('D12_actual_driver_drift',tool=shadow,guard='Adapter source drift',notes='Own scratch copy differs by a harmless comment; original portable tool is unmodified.')
    def bad_alias(c,f):
        t=f/'own_fake_tree';physical=t/'.lake/packages/PFR/PFR';physical.mkdir(parents=True)
        wrong=f/'wrong_alias_target';wrong.mkdir();(t/'PFR').symlink_to(wrong,target_is_directory=True)
        c['tree']=str(t)
    # This case reaches the namespace alias guard with its otherwise correct physical output.
    folder=case('D13_namespace_alias_conflict');cfg=json.loads(json.dumps(cfg0));bad_alias(cfg,folder)
    cp=folder/'config.json';write_json(cp,cfg)
    obj=Path(cfg['tree'])/(relative.removesuffix('.lean')+'.olean')
    run(folder.name,[entry,relative,'-o',obj],CLONE,cfg=cp)
    assert not (folder/'capture.argv.json').exists()
    noncanonical=relative.replace('/Set/Basic.lean','/Set/../Set/Basic.lean')
    assert noncanonical!=relative
    driver('D14_noncanonical_source_path',args=[noncanonical,'-o',str(output)],guard='Source is outside the fixed PFR closure')

    # A trusted-runtime-config boundary control: unused provenance fields are not a
    # content signature. It changes no execution argument or selected source.
    info=driver('I01_unused_pin_metadata_drift',change=lambda c,f:c.update(pfr_package_pin='0'*40),expect=True,
                notes='Informational: runtime config is trusted input. Unused pin provenance has no independent runtime signature; execution-relevant checks still pass.')
    assert info['capture']['argv']==expected
    pin_tools()
    assert sha(fake)==fake_hash
    assert not list(ROOT.rglob('*.olean')),'No compiled or fake olean product may be created'
    assert all(sha(p)==h for p,h in static_before.items()),'Static supplement changed'
    assert all(sha(p)==h for p,h in source_metadata.items()),'Pinned clone/package inputs changed'
    assert all(r['expectation_met'] for r in results),[r['case'] for r in results if not r['expectation_met']]
    summary={'status':'NON_NATIVE_INVOCATION_GUARD_SIMULATION_COMPLETE',
       'portable_tool_sha256':PINS,'cases':len(results),'expectations_met':sum(r['expectation_met'] for r in results),
       'prepare_cases':sum(r['case'].startswith('P') for r in results),
       'driver_cases':sum(r['case'].startswith('D') for r in results),
       'informational_boundary_controls':sum(r['case'].startswith('I') for r in results),
       'fake_target_executions':sum(r['capture_exists'] for r in results),
       'no_olean_products':True,'portable_tools_unchanged':True,'package_source_config_unchanged':True,
       'source_metadata_sha256':source_metadata,'static_supplement_sha256':static_before,
       'limitations':['Simulation invokes only an own argv-capturing executable. No Lean/cache/build/app process, native compilation or module/constant-owner check occurred.',
         'Inventory mutation cases are rejected by the outer frozen-manifest/leaf hash guard; they do not separately exercise bypassed inner duplicate/order assertions.',
         'Runtime config is trusted root-generated input; its unused pfr_package_pin metadata field is not itself revalidated or signed at every invocation.',
         'No portable tool edit or bug correction was made by this harness.']}
    write_json(ROOT/'SUMMARY.json',summary)
    write_json(ROOT/'results.json',results)
    files=sorted(p for p in ROOT.rglob('*') if p.is_file() and not p.is_symlink())
    write_json(ROOT/'MANIFEST.json',{'status':summary['status'],'portable_tool_sha256':PINS,
        'own_harness_sha256':sha(__file__),'files':[{'path':str(p.relative_to(ROOT)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in files],
        'native_execution':False,'compiled_outputs':False,'original_source_package_and_tool_writes':False})
    print(json.dumps({k:v for k,v in summary.items() if k not in ['source_metadata_sha256','static_supplement_sha256']},indent=2))


if __name__=='__main__':main()
