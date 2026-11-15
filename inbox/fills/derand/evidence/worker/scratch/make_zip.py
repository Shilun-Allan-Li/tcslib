"""Create a deterministic derand-root ZIP and verify every entry and CRC."""
import hashlib
import json
from pathlib import Path
import sys
import zipfile

root = Path(sys.argv[1]).resolve()
destination = Path(sys.argv[2]).resolve()
assert root.name == 'derand' and (root / 'SHA256SUMS').is_file()
assert destination.suffix == '.zip' and not destination.exists()
assert not destination.is_relative_to(root)
files = sorted(p for p in root.rglob('*') if p.is_file())
assert files and all(not p.is_symlink() for p in files)
expected = {'derand/' + p.relative_to(root).as_posix(): p for p in files}
with zipfile.ZipFile(destination, 'x', compression=zipfile.ZIP_DEFLATED,
                     compresslevel=6, allowZip64=True) as archive:
    for name, path in expected.items():
        info = zipfile.ZipInfo(name, date_time=(2026, 11, 15, 0, 0, 0))
        info.create_system = 3
        info.external_attr = (0o100000 | (path.stat().st_mode & 0o777)) << 16
        info.compress_type = zipfile.ZIP_DEFLATED
        archive.writestr(info, path.read_bytes(), compress_type=zipfile.ZIP_DEFLATED,
                         compresslevel=6)
with zipfile.ZipFile(destination) as archive:
    assert archive.testzip() is None
    assert len(archive.namelist()) == len(expected)
    assert set(archive.namelist()) == set(expected)
    assert all(name.startswith('derand/') and '..' not in Path(name).parts
               for name in archive.namelist())
    for name, source in expected.items():
        assert hashlib.sha256(archive.read(name)).digest() == \
            hashlib.sha256(source.read_bytes()).digest(), name
result = dict(zip=str(destination), root='derand/', entries=len(files),
              payload_bytes=sum(p.stat().st_size for p in files),
              zip_bytes=destination.stat().st_size,
              sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),
              crc='PASS', exact_entry_set='PASS', every_entry_sha256='PASS')
print(json.dumps(result, indent=2))
