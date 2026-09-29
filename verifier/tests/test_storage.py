from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from linux_exec import bounded_tmpfs
from storage import writable_filesystems
from verify import linux_command


@unittest.skipUnless(sys.platform == 'linux', 'Linux sandbox')
class StorageTests(unittest.TestCase):
    def test_disk_directory_is_not_accepted_as_bounded_tmpfs(self):
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(RuntimeError):
                bounded_tmpfs(Path(directory), 1 << 30, 10000)

    def test_linux_job_only_has_bounded_writable_mounts(self):
        project = Path('/srv/sig-golf/work/test/project')
        command, _ = linux_command(['true'], project,
                                  {'COMPARATOR_LANDRUN': '/bin/true',
                                   'COMPARATOR_LEAN4EXPORT': '/bin/true'}, [])
        props = [command[index + 1] for index, arg in enumerate(command[:-1]) if arg == '-p']
        self.assertFalse(any(prop.startswith('ReadWritePaths=') for prop in props))
        self.assertIn(f'BindReadOnlyPaths={project}/.lake-seed/packages:{project}/.lake/packages', props)
        for path, size, inodes in writable_filesystems(project):
            mount = next(prop for prop in props if prop.startswith(f'TemporaryFileSystem={path}:'))
            self.assertIn(f'size={size},', mount)
            self.assertIn(f'nr_inodes={inodes},', mount)
        self.assertTrue(any('@mount' in prop for prop in props if prop.startswith('SystemCallFilter=')))

    def test_kernel_enforces_bytes_and_inodes(self):
        probe = subprocess.run(['unshare', '--user', '--map-root-user', '--mount', 'true'],
                               capture_output=True)
        if probe.returncode:
            self.skipTest('unprivileged mount namespaces unavailable')
        # Exercise the real kernel, not a disk-use poll or mocked statvfs values.
        code = r'''
import errno
import os
from pathlib import Path
import subprocess
import sys
sys.path.insert(0, sys.argv[1])
from linux_exec import bounded_tmpfs
path = Path(sys.argv[2])
subprocess.run(['mount', '-t', 'tmpfs', '-o', 'size=1M,nr_inodes=64', 'tmpfs', str(path)], check=True)
bounded_tmpfs(path, 1 << 20, 64)
for byte_limit, inode_limit in ((1 << 19, 64), (1 << 20, 32)):
    try:
        bounded_tmpfs(path, byte_limit, inode_limit)
    except RuntimeError:
        pass
    else:
        raise AssertionError('oversized filesystem accepted')
with (path / 'large').open('wb') as stream:
    try:
        os.posix_fallocate(stream.fileno(), 0, 2 << 20)
    except OSError as exc:
        assert exc.errno == errno.ENOSPC, exc
    else:
        raise AssertionError('byte quota not enforced')
for index in range(100):
    try:
        (path / str(index)).touch()
    except OSError as exc:
        assert exc.errno == errno.ENOSPC, exc
        break
else:
    raise AssertionError('inode quota not enforced')

# Exercise the same seed/read-only dependency layout used by the launcher.
subprocess.run(['umount', str(path)], check=True)
project = path / 'project'
seed = project / '.lake-seed'
for name in ('build', 'config', 'packages'):
    (seed / name).mkdir(parents=True)
    (seed / name / 'trusted').write_text(name)
(project / '.lake').mkdir()
subprocess.run(['mount', '--bind', str(project), str(project)], check=True)
subprocess.run(['mount', '-o', 'remount,bind,ro', str(project)], check=True)
lake = project / '.lake'
subprocess.run(['mount', '-t', 'tmpfs', '-o', 'size=1M,nr_inodes=64', 'tmpfs', str(lake)], check=True)
(lake / 'packages').mkdir()
subprocess.run(['mount', '--bind', str(seed / 'packages'), str(lake / 'packages')], check=True)
subprocess.run(['mount', '-o', 'remount,bind,ro', str(lake / 'packages')], check=True)
os.chdir(project)
import linux_exec
linux_exec.writable_filesystems = lambda _: [(lake, 1 << 20, 64)]
linux_exec.prepare_build_cache()
assert (lake / 'build/trusted').read_text() == 'build'
assert (lake / 'config/trusted').read_text() == 'config'
(lake / 'build/output').write_text('candidate output')
for target in (seed / 'build/trusted', lake / 'packages/trusted'):
    try:
        target.write_text('overwrite')
    except OSError as exc:
        assert exc.errno == errno.EROFS, exc
    else:
        raise AssertionError('trusted cache is writable')
'''
        with tempfile.TemporaryDirectory() as directory:
            result = subprocess.run(['unshare', '--user', '--map-root-user', '--mount',
                                     sys.executable, '-c', code, str(Path(__file__).resolve().parents[1]), directory],
                                    capture_output=True, text=True, timeout=30)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
