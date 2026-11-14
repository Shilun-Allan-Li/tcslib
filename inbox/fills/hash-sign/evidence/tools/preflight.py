import os
import pathlib
import re
import subprocess

def run(args):
    print('$ ' + ' '.join(args), flush=True)
    try:
        p = subprocess.run(args, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        print(p.stdout, end='', flush=True)
        print('exit:', p.returncode, flush=True)
        return p.stdout
    except FileNotFoundError as e:
        print(str(e), flush=True)
        return ''

run(['date', '-u'])
run(['uname', '-a'])
run(['nproc'])
run(['sysctl', '-n', 'hw.ncpu'])
total = int(run(['sysctl', '-n', 'hw.memsize']).strip())
vm = run(['vm_stat'])
page = int(re.search(r'page size of (\d+) bytes', vm)[1])
fields = {a.strip(): int(b) for a, b in re.findall(r'^([^:\n]+):\s+(\d+)\.', vm, re.M)}
used = page * sum(fields[k] for k in ['Anonymous pages', 'Pages wired down', 'Pages occupied by compressor'])
headroom = total - used
print('macOS native equivalent; Linux cgroups and /proc/meminfo unavailable.')
print(f'physical_bytes={total}; non_file_used_bytes={used}; headroom_bytes={headroom}')
run(['memory_pressure', '-Q'])
paths = ['/private/tmp/hash-sign-fill/repo', '/private/tmp/hash-sign-fill/delivery', os.environ.get('TMPDIR', '/private/tmp')]
run(['df', '-B1'] + paths)
run(['df', '-T'] + paths)
run(['df', '-k'] + paths)
run(['mount'])
for path in paths:
    st = os.statvfs(path)
    free = st.f_bavail * st.f_frsize
    print(f'{path}: free_bytes={free}; initial_disk_floor_bytes={12 * 1024**3}')
    if free < 12 * 1024**3:
        raise SystemExit('E-RES disk floor')
if headroom < 4 * 1024**3:
    raise SystemExit('E-RES memory floor')
print('PREFLIGHT PASS (macOS native resource readings)')
