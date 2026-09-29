"""The only writable filesystems exposed to a Linux verification job."""
from pathlib import Path

BUILD_BYTES = 4 * 1024**3
BUILD_INODES = 100_000
TEMP_BYTES = 256 * 1024**2
TEMP_INODES = 16_384
SHM_BYTES = 64 * 1024**2
SHM_INODES = 4096


def writable_filesystems(project: Path) -> list[tuple[Path, int, int]]:
    return [(project / '.lake', BUILD_BYTES, BUILD_INODES),
            (Path('/tmp'), TEMP_BYTES, TEMP_INODES),
            (Path('/var/tmp'), TEMP_BYTES, TEMP_INODES),
            (Path('/dev/shm'), SHM_BYTES, SHM_INODES)]
