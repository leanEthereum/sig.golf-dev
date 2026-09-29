#!/usr/bin/env python3
"""Refuse comparator startup if systemd did not apply the mandatory Linux isolation."""
from __future__ import annotations

import os
from pathlib import Path
import shutil
import socket
import sys

from storage import writable_filesystems


def pid_namespace() -> str | None:
    """This process's PID namespace, or None when /proc cannot tell."""
    try:
        return str(os.stat("/proc/self/ns/pid").st_ino)
    except OSError:
        return None


def bounded_tmpfs(path: Path, max_bytes: int, max_inodes: int) -> None:
    """Fail closed if a requested mount or either kernel quota was ignored."""
    escaped = str(path).replace('\\', '\\134').replace(' ', '\\040').replace('\t', '\\011').replace('\n', '\\012')
    mounts = [line.split(' - ', 1) for line in Path('/proc/self/mountinfo').read_text().splitlines()]
    if not any(left.split()[4] == escaped and right.split()[0] == 'tmpfs' for left, right in mounts):
        raise RuntimeError(f'{path} is not a private tmpfs mount')
    stats = os.statvfs(path)
    if (stats.f_flag & os.ST_RDONLY or not 0 < stats.f_blocks * stats.f_frsize <= max_bytes or
            not 0 < stats.f_files <= max_inodes):
        raise RuntimeError(f'{path} does not enforce its storage limits')


def prepare_build_cache() -> None:
    project = Path.cwd()
    for path, size, inodes in writable_filesystems(project):
        bounded_tmpfs(path, size, inodes)
    for path in (project / '.lake-seed', project / '.lake/packages'):
        if not os.statvfs(path).f_flag & os.ST_RDONLY:
            raise RuntimeError(f'{path} must be read-only')
    # Dependencies stay on the read-only host filesystem; only the small root
    # build and Lake configuration caches are copied into the bounded tmpfs.
    for name in ('build', 'config'):
        source = project / '.lake-seed' / name
        if source.exists():
            shutil.copytree(source, project / '.lake' / name, symlinks=True)


def isolation_check() -> None:
    if sys.platform != "linux" or os.geteuid() == 0:
        raise RuntimeError("sandbox launcher requires an unprivileged Linux process")
    host_dev = os.environ.get("SIG_VERIFIER_HOST_DEV")
    host_shm = os.environ.get("SIG_VERIFIER_HOST_SHM_DEV")
    if not host_dev or str(Path("/dev").stat().st_dev) == host_dev:
        raise RuntimeError("systemd failed to provide private devices; refusing to compile")
    if host_shm and Path("/dev/shm").exists() and str(Path("/dev/shm").stat().st_dev) == host_shm:
        raise RuntimeError("systemd failed to isolate shared memory; refusing to compile")
    for path in (Path.cwd(), Path(__file__).resolve(), Path.home()):
        if not os.statvfs(path).f_flag & os.ST_RDONLY:
            raise RuntimeError(f"systemd failed to mount {path} read-only; refusing to compile")
    host_pidns = os.environ.get("SIG_VERIFIER_HOST_PIDNS")
    if not host_pidns or pid_namespace() in (None, host_pidns):
        raise RuntimeError("systemd failed to give the job its own PID namespace; refusing to compile")
    try:
        list(Path("/sys/kernel").iterdir())
    except OSError:
        pass
    else:
        raise RuntimeError("systemd failed to hide /sys/kernel; refusing to compile")
    if Path("/etc/sig-golf").exists():
        try:
            list(Path("/etc/sig-golf").iterdir())
        except OSError:
            pass
        else:
            raise RuntimeError("systemd failed to hide /etc/sig-golf; refusing to compile")
    for family, kind in ((socket.AF_UNIX, socket.SOCK_STREAM),
                         (socket.AF_INET, socket.SOCK_STREAM),
                         (socket.AF_INET, socket.SOCK_DGRAM),
                         (socket.AF_INET6, socket.SOCK_STREAM)):
        try:
            sock = socket.socket(family, kind)
        except OSError:
            continue
        sock.close()
        raise RuntimeError("systemd failed to disable networking; refusing to compile")
    try:
        # A zero signal is harmless, but uses the same syscall that could terminate a
        # same-UID worker. The supervisor lives outside this filter and can still kill us.
        os.kill(os.getpid(), 0)
    except OSError:
        pass
    else:
        raise RuntimeError("systemd failed to disable process signals; refusing to compile")


def main() -> int:
    try:
        isolation_check()
        prepare_build_cache()
        if len(sys.argv) < 2:
            raise RuntimeError("sandbox launcher needs a command")
        os.execvpe(sys.argv[1], sys.argv[1:], os.environ)
    except (OSError, RuntimeError) as exc:
        print(f"sandbox launch refused: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
