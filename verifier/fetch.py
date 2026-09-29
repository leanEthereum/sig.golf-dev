"""Fetch bounded metadata first, then admitted blobs at a frozen public GitHub commit.

No Git pack is downloaded: filtering blobs does not bound the size of a pack or
its tree objects. This process has no GitHub credentials.
"""
from __future__ import annotations

import hashlib
import json
import re
import time
import urllib.error
import urllib.parse
import urllib.request
from pathlib import Path

from check_submission import (MAX_FILES, MAX_FILE_BYTES, MAX_TOTAL_BYTES,
                              admitted_directory, admitted_file)

SHA = re.compile(r"[0-9a-f]{40}|[0-9a-f]{64}")
MAX_TREE_OUTPUT = 4 * 1024 * 1024
FETCH_SECONDS = 600


class FetchError(ValueError):
    pass


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        raise FetchError("GitHub redirected a frozen-source request")


def download(url: str, limit: int, deadline: float) -> bytes:
    """Bound the actual body, even with no or dishonest Content-Length."""
    remaining = deadline - time.monotonic()
    if remaining <= 0:
        raise FetchError("source fetch timed out")
    request = urllib.request.Request(url, headers={
        'Accept': 'application/vnd.github+json' if url.startswith('https://api.github.com/') else '*/*',
        'Accept-Encoding': 'identity', 'User-Agent': 'sig-golf-beta-verifier',
        'X-GitHub-Api-Version': '2022-11-28'})
    try:
        with urllib.request.build_opener(NoRedirect()).open(request, timeout=min(30, remaining)) as response:
            length = response.headers.get('Content-Length')
            if length is not None and (not length.isdecimal() or int(length) > limit):
                raise FetchError("source response exceeds its byte limit")
            result = bytearray()
            while True:
                if time.monotonic() >= deadline:
                    raise FetchError("source fetch timed out")
                chunk = response.read1(min(65536, limit - len(result) + 1))
                if not chunk:
                    break
                result.extend(chunk)
                if len(result) > limit:
                    raise FetchError("source response exceeds its byte limit")
            return bytes(result)
    except (OSError, urllib.error.URLError) as exc:
        raise FetchError(f"source download failed: {exc}") from exc


def metadata(path: str, deadline: float) -> dict:
    try:
        value = json.loads(download('https://api.github.com' + path, MAX_TREE_OUTPUT, deadline))
    except (ValueError, UnicodeError) as exc:
        raise FetchError(f"invalid GitHub metadata: {exc}") from exc
    if not isinstance(value, dict):
        raise FetchError("GitHub metadata must be an object")
    return value


def tree_entries(value: dict) -> list[dict]:
    if (value.get('truncated') is not False or not isinstance(value.get('tree'), list) or
            not all(isinstance(entry, dict) for entry in value['tree'])):
        raise FetchError("GitHub returned an incomplete or invalid tree")
    return value['tree']


def object_id(value) -> str:
    if not isinstance(value, str) or not SHA.fullmatch(value):
        raise FetchError("invalid Git object ID")
    return value


def fetch_pr(repository: str, number: int, commit: str, destination: Path) -> str:
    """Validate all paths and sizes before downloading any candidate file."""
    if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9-]*/[A-Za-z0-9_.-]+", repository):
        raise FetchError("invalid repository")
    if type(number) is not int or number < 1:
        raise FetchError("invalid PR number")
    object_id(commit)
    if destination.exists():
        raise FetchError("destination must be new")
    deadline = time.monotonic() + FETCH_SECONDS
    base = f'/repos/{repository}'
    pr = metadata(f'{base}/pulls/{number}', deadline)
    if not isinstance(pr.get('head'), dict) or pr['head'].get('sha') != commit:
        raise FetchError("PR head changed during fetch")
    info = metadata(f'{base}/git/commits/{commit}', deadline)
    if not isinstance(info.get('tree'), dict):
        raise FetchError("GitHub did not return the commit tree")
    tree = object_id(info['tree'].get('sha'))
    root = tree_entries(metadata(f'{base}/git/trees/{tree}', deadline))
    roots = [entry for entry in root if entry.get('path') == 'submission']
    if len(roots) != 1 or roots[0].get('type') != 'tree' or roots[0].get('mode') != '040000':
        raise FetchError("PR must contain a submission directory")
    subtree = object_id(roots[0].get('sha'))
    entries = tree_entries(metadata(f'{base}/git/trees/{subtree}?recursive=1', deadline))
    if not entries or len(entries) > MAX_FILES:
        raise FetchError("submission is empty or has too many entries")
    selected = []
    seen = set()
    total = 0
    for entry in entries:
        name = entry.get('path')
        if not isinstance(name, str) or not name or name in seen:
            raise FetchError("invalid or duplicate submission path")
        seen.add(name)
        path = Path(name)
        if path.is_absolute() or '..' in path.parts or path.as_posix() != name:
            raise FetchError(f"invalid submission path: {name!r}")
        oid = object_id(entry.get('sha'))
        if entry.get('type') == 'tree' and entry.get('mode') == '040000' and admitted_directory(name):
            continue
        if (entry.get('type') != 'blob' or entry.get('mode') not in {'100644', '100755'} or
                not admitted_file(name)):
            raise FetchError(f"invalid submission entry: {name!r}")
        size = entry.get('size')
        if type(size) is not int or not 0 <= size <= MAX_FILE_BYTES:
            raise FetchError(f"{name}: invalid size or file exceeds 8 MiB")
        total += size
        if total > MAX_TOTAL_BYTES:
            raise FetchError("submission exceeds 16 MiB")
        selected.append((path, oid, size))
    if not selected:
        raise FetchError("submission contains no files")
    destination.mkdir(parents=True)
    for path, oid, size in selected:
        url = f'https://raw.githubusercontent.com/{repository}/{commit}/submission/' + urllib.parse.quote(path.as_posix())
        raw = download(url, size, deadline)
        digest = hashlib.sha1() if len(oid) == 40 else hashlib.sha256()
        digest.update(f'blob {len(raw)}\0'.encode())
        digest.update(raw)
        if len(raw) != size or digest.hexdigest() != oid:
            raise FetchError("downloaded blob does not match its frozen Git object")
        output = destination / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_bytes(raw)
    return commit
