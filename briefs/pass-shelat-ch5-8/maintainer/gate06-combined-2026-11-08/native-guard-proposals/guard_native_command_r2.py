"""Root-reviewed host guard for a pinned, serial Rule10/probe command.

This does not interpret Lean outcomes. It records and returns the real command's
status, including expected negative controls and retained source seal failures.
Fresh output directories only; no retries, resumes, or other-process signals.
R2 retains R1 unchanged and repairs signal lifecycle and post-wait pin checks.
"""
from pathlib import Path
import datetime as dt
import hashlib
import importlib.util
import json
import os
import signal
import subprocess
import sys
import time

ROOT = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4')
AREA = ROOT / '.lake/ps-maintainer/gate06-combined-20261108'
TREE = AREA / 'oleans-r1'
TOOLS = AREA / 'rule10-prep/proposed-tools'
HEAD = 'a495f3953afff46ad5dec2d29ac8a7f55bd8ae37'
NATIVE = AREA / 'native-runtime-proposal/run_combined_native.py'
NATIVE_SHA = '64b5b2ff2260a48eef55dcf77bdb5c4125459170b28c30499f60a93de7da3c95'
ALLOWED = {
    str(TOOLS / 'check_probe_v2.py'): 'c685d6aa01b1b7e44115e88781d1634b3b3cdda512acc702eeba5e810f767179',
    str(TOOLS / 'run_gate06_final_native.py'): '0a8b5ebc13d5b2cd4f613fbecb83a357daad285ef84e29774180378f3430a52b',
}
LEASE = AREA / 'native-runner.lease.json'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def now():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def require(test, reason):
    if not test:
        raise RuntimeError(reason)


def save(path, obj):
    with path.open('x') as stream:
        stream.write(json.dumps(obj, indent=2) + '\n')


def main():
    require(len(sys.argv) >= 4, 'usage: guard_native_command_r2.py NEW_LABEL PINNED_TOOL ARGS...')
    label, tool = sys.argv[1], Path(sys.argv[2])
    require(label.replace('-', '').replace('_', '').isalnum(), 'unsafe output label')
    require(str(tool) in ALLOWED and tool.is_file() and not tool.is_symlink(), 'not an allowed reviewed tool')
    expected = ALLOWED[str(tool)]
    require(sha(tool) == expected and sha(NATIVE) == NATIVE_SHA, 'reviewed tool bytes changed')
    sys.dont_write_bytecode = True
    spec = importlib.util.spec_from_file_location('g06_reviewed_host_guards', NATIVE)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    inventory = AREA / 'native-bootstrap-r1/source-start.json'
    inventory_sha = '7f606ceb1c33a018ef833ee779457f0e447d334b442acab746b4a8899f82191c'
    require(sha(inventory) == inventory_sha, 'bootstrap source inventory changed')
    source_rows = json.loads(inventory.read_text())
    require(len(source_rows) == 1109, 'incomplete frozen source inventory')
    boot_result = AREA / 'native-bootstrap-r1/RESULT.json'
    result = json.loads(boot_result.read_text())
    require(result['passed'] is True and result['head'] == HEAD and result['phase'] == 'bootstrap', 'completed bootstrap required')
    boot_sha = sha(boot_result)
    self_sha = sha(Path(__file__))
    def quick_pins():
        require(sha(tool) == expected and sha(NATIVE) == NATIVE_SHA and sha(Path(__file__)) == self_sha, 'reviewed tool bytes changed')
        require(sha(inventory) == inventory_sha and sha(boot_result) == boot_sha, 'bootstrap evidence changed')
        require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == HEAD, 'wrong source HEAD')
        require(not subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=ROOT).strip(), 'tracked source dirty')
        actual = {f.relative_to(ROOT).as_posix() for f in (ROOT / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean', 'audits/pass-shelat/Checks.lean'}
        require(actual == set(source_rows), 'library source set changed')
        for rel, digest in source_rows.items():
            require(sha(ROOT / rel) == digest, 'library source changed: ' + rel)
    quick_pins()
    out = AREA / 'guarded-native-r1' / label
    out.mkdir(parents=True, exist_ok=False)
    own = {'pid': os.getpid(), 'utc': now(), 'guard_source_sha256': sha(Path(__file__)), 'label': label}
    # Install cleanup before acquiring the same exclusive lease as bootstrap/local.
    # A signal raises through the protected lifecycle; only our child group is stopped.
    proc = None
    lease_owned = False
    def stop_signal(signum, _frame):
        raise InterruptedError('Guard received signal ' + str(signum))
    previous_handlers = {sig: signal.signal(sig, stop_signal) for sig in (signal.SIGTERM, signal.SIGHUP)}
    try:
        save(LEASE, own)
        lease_owned = True
        helper.wait_idle(out)
        resources = helper.resources()
        quick_pins()
        require(not helper.native_processes(), 'host became busy before command start')
        env = dict(os.environ)
        for key in ('LEAN_PATH', 'LEAN_SRC_PATH', 'LEAN_SYSROOT', 'LEAN_OPTS', 'ELAN_TOOLCHAIN', 'PFR_BOOTSTRAP_CONFIG'):
            env.pop(key, None)
        real = Path('/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/bin/lean')
        require(sha(real) == '2974847fff2e2621502841f4c2dbac4035b4847d6060a4f2087cbc0d04005e37', 'Lean binary changed')
        env['PATH'] = str(real.parent) + ':' + str(Path.home() / '.elan/bin') + ':/opt/homebrew/bin:/usr/local/bin:/usr/bin:/bin:/usr/sbin:/sbin'
        env['TCSLIB_OLEANS'] = str(TREE)
        command = [sys.executable, '-I', str(tool), *sys.argv[3:]]
        start = dict(own, command=command, tool_sha256=expected, host_guard_sha256=NATIVE_SHA,
                     head=HEAD, source_inventory_sha256=inventory_sha, bootstrap_result_sha256=boot_sha,
                     resources=resources, TCSLIB_OLEANS=str(TREE), PATH=env['PATH'])
        save(out / 'start.json', start)
        interrupted = None
        with (out / 'launcher.log').open('xb') as stream:
            try:
                quick_pins()
                require(not helper.native_processes(), 'host became busy immediately before launch')
                proc = subprocess.Popen(command, cwd=ROOT, env=env, stdin=subprocess.DEVNULL,
                                        stdout=stream, stderr=subprocess.STDOUT, start_new_session=True)
                save(out / 'child.json', {'pid': proc.pid, 'pgid': proc.pid, 'utc': now()})
                last_watch = 0.0
                while proc.poll() is None:
                    if time.monotonic() - last_watch >= 1:
                        foreign = [p for p in helper.native_processes() if p['pgid'] != proc.pid]
                        require(not foreign, 'HOST_COLLISION: ' + json.dumps(foreign))
                        last_watch = time.monotonic()
                    time.sleep(0.1)
                require(not helper.group_members(proc.pid), 'live descendant after command exit')
            except BaseException as error:
                interrupted = repr(error)
                if proc is not None:
                    # The method signals only this newly sessioned child group.
                    helper.Run.stop_own_group(None, proc)
        rc = proc.returncode if proc is not None else None
        quick_pins()
        save(out / 'RESULT.json', {'utc': now(), 'command_rc': rc, 'interrupted': interrupted,
             'head': HEAD, 'tool_sha256': expected, 'launcher_log_sha256': sha(out / 'launcher.log'),
             'outcome_interpreted': False, 'other_processes_signalled': False})
        print(json.dumps({'guard_output': str(out), 'command_rc': rc, 'interrupted': interrupted}), flush=True)
        return 2 if interrupted is not None else rc
    except BaseException as error:
        if proc is not None and (proc.poll() is None or helper.group_members(proc.pid)):
            helper.Run.stop_own_group(None, proc)
        save(out / 'STOP.json', {'utc': now(), 'error': repr(error), 'own_child_pid': proc.pid if proc else None})
        raise
    finally:
        if lease_owned and LEASE.is_file() and json.loads(LEASE.read_text()).get('pid') == os.getpid():
            LEASE.unlink()
        for sig, previous in previous_handlers.items():
            signal.signal(sig, previous)


if __name__ == '__main__':
    sys.exit(main())
