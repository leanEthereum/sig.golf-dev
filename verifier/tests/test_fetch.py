import hashlib
import io
import sys
import tempfile
import time
import unittest
from pathlib import Path
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import fetch

COMMIT = 'a' * 40


def blob(name, raw):
    oid = hashlib.sha1(f'blob {len(raw)}\0'.encode() + raw).hexdigest()
    return {'path': name, 'type': 'blob', 'mode': '100644', 'sha': oid, 'size': len(raw)}


class FetchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.destination = Path(self.temp.name) / 'submission'
        self.raw = b'import SigGolf\n'
        self.entries = [blob('Solution.lean', self.raw)]
        self.truncated = False
        self.head = COMMIT

    def tearDown(self):
        self.temp.cleanup()

    def metadata(self, path, deadline):
        if '/pulls/' in path:
            return {'head': {'sha': self.head}}
        if '/git/commits/' in path:
            return {'tree': {'sha': 'b' * 40}}
        if path.endswith('b' * 40):
            return {'truncated': False, 'tree': [
                {'path': 'submission', 'type': 'tree', 'mode': '040000', 'sha': 'c' * 40}]}
        return {'truncated': self.truncated, 'tree': self.entries}

    def run_fetch(self, raw=None):
        with patch.object(fetch, 'metadata', side_effect=self.metadata), \
                patch.object(fetch, 'download', return_value=self.raw if raw is None else raw) as download:
            fetch.fetch_pr('owner/repo', 1, COMMIT, self.destination)
            return download

    def rejected_before_blob_download(self):
        with patch.object(fetch, 'metadata', side_effect=self.metadata), \
                patch.object(fetch, 'download') as download:
            with self.assertRaises(fetch.FetchError):
                fetch.fetch_pr('owner/repo', 1, COMMIT, self.destination)
            download.assert_not_called()
        self.assertFalse(self.destination.exists())

    def test_frozen_blob_is_hashed_and_download_is_bounded(self):
        download = self.run_fetch()
        self.assertEqual((self.destination / 'Solution.lean').read_bytes(), self.raw)
        url, size, _ = download.call_args.args
        self.assertEqual(url, f'https://raw.githubusercontent.com/owner/repo/{COMMIT}/submission/Solution.lean')
        self.assertEqual(size, len(self.raw))

    def test_oversized_blob_rejected_before_transfer(self):
        self.entries[0]['size'] = fetch.MAX_FILE_BYTES + 1
        self.rejected_before_blob_download()

    def test_aggregate_limit_checked_before_first_transfer(self):
        self.entries = [dict(blob(f'SigGolfCandidate/M{i}.lean', b''), size=fetch.MAX_FILE_BYTES)
                        for i in range(3)]
        self.rejected_before_blob_download()

    def test_entry_count_includes_directories(self):
        self.entries = [{'path': f'SigGolfCandidate/M{i}', 'type': 'tree',
                         'mode': '040000', 'sha': 'd' * 40} for i in range(fetch.MAX_FILES + 1)]
        self.rejected_before_blob_download()

    def test_symlinks_submodules_and_paths_rejected_before_transfer(self):
        for change in ({'mode': '120000'}, {'mode': '160000', 'type': 'commit'},
                       {'path': '../Solution.lean'}, {'path': '/Solution.lean'},
                       {'path': 'SigGolfCandidate//M.lean'}, {'path': 'lakefile.lean'},
                       {'path': 'images/extra.data'}, {'size': True}):
            with self.subTest(change=change):
                self.entries = [dict(blob('Solution.lean', self.raw), **change)]
                self.rejected_before_blob_download()

    def test_changed_head_and_truncated_tree_fail_closed(self):
        self.head = 'd' * 40
        self.rejected_before_blob_download()
        self.head = COMMIT
        self.truncated = True
        self.rejected_before_blob_download()

    def test_wrong_blob_rejected_even_when_size_matches(self):
        with self.assertRaisesRegex(fetch.FetchError, 'frozen Git object'):
            self.run_fetch(b'x' * len(self.raw))
        self.assertFalse((self.destination / 'Solution.lean').exists())

    def test_candidate_module_paths_are_admitted(self):
        self.entries = [{'path': 'SigGolfCandidate', 'type': 'tree', 'mode': '040000', 'sha': 'd' * 40},
                        {'path': 'SigGolfCandidate/Nested', 'type': 'tree', 'mode': '040000', 'sha': 'e' * 40},
                        blob('SigGolfCandidate/Nested/Helper.lean', self.raw)]
        self.run_fetch()
        self.assertEqual((self.destination / 'SigGolfCandidate/Nested/Helper.lean').read_bytes(), self.raw)


class Response(io.BytesIO):
    def __init__(self, body, length=None):
        super().__init__(body)
        self.headers = {} if length is None else {'Content-Length': length}
        self.consumed = 0

    def read1(self, size):
        chunk = super().read1(size)
        self.consumed += len(chunk)
        return chunk


class DownloadTests(unittest.TestCase):
    def test_missing_or_false_content_length_cannot_bypass_actual_limit(self):
        for length in (None, '1', '1000000'):
            with self.subTest(length=length):
                response = Response(b'x' * 1000000, length)
                with patch.object(fetch.urllib.request, 'build_opener') as opener:
                    opener.return_value.open.return_value = response
                    with self.assertRaisesRegex(fetch.FetchError, 'byte limit'):
                        fetch.download('https://raw.githubusercontent.com/o/r/file', 1024, time.monotonic() + 60)
                self.assertLessEqual(response.consumed, 1025)

    def test_expired_deadline_does_not_connect(self):
        with patch.object(fetch.urllib.request, 'build_opener') as opener:
            with self.assertRaisesRegex(fetch.FetchError, 'timed out'):
                fetch.download('https://api.github.com/repos/o/r', 1024, time.monotonic() - 1)
            opener.assert_not_called()

    def test_redirects_are_rejected(self):
        with self.assertRaises(fetch.FetchError):
            fetch.NoRedirect().redirect_request(None, None, 302, '', {}, 'https://example.com')


if __name__ == '__main__':
    unittest.main()
