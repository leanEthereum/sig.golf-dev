import json
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from check_submission import check
from images import IMAGE_FILES, MAX_PROGRAM_BYTES


class PolicyTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        (self.root / 'SigGolfCandidate').mkdir()
        (self.root / 'images').mkdir()
        for name in IMAGE_FILES:
            (self.root / name).write_bytes(b'')
        (self.root / 'Solution.lean').write_text('import SigGolfCandidate.Helper\n')
        (self.root / 'SigGolfCandidate' / 'Helper.lean').write_text('import SigGolf\n')
        self.claim = {'S': 8, 'W': 8, 'K': 1 << 17, 'C': 100,
                      'layout': {'message': 0, 'secret_key': 32, 'public_key': 64,
                                 'cache': 96, 'signature': 131168, 'witness': 131176}}
        self.write_claim()

    def write_claim(self):
        (self.root / 'claim.json').write_text(json.dumps(self.claim))

    def tearDown(self):
        self.temp.cleanup()

    def test_valid_layout_and_score(self):
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.assertEqual(value['score'], 800)

    def test_cross_import_is_rejected(self):
        (self.root / 'SigGolfCandidate' / 'Helper.lean').write_text('import SigGolfCandidateX.Helper\n')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the allowed modules', value['errors'][0])

    def test_module_header_cannot_hide_public_imports(self):
        for header in ('module', 'module -- comment', '\ufeffmodule', '/- comment -/ module'):
            with self.subTest(header=header):
                (self.root / 'Solution.lean').write_text(header + '\npublic import Lake\n')
                value = check(self.root)
                self.assertFalse(value['ok'])
                self.assertTrue(any('alternate module headers' in error for error in value['errors']))

    def test_generated_images_import_is_allowed(self):
        (self.root / 'Solution.lean').write_text('import SigGolf.Images\n')
        self.assertTrue(check(self.root)['ok'])

    def test_missing_image_is_rejected(self):
        (self.root / 'images/verify.data').unlink()
        self.assertFalse(check(self.root)['ok'])

    def test_instruction_alignment_and_combined_image_size(self):
        code = self.root / 'images/sign.code'
        data = self.root / 'images/sign.data'
        code.write_bytes(b'\x73')
        self.assertFalse(check(self.root)['ok'])
        code.write_bytes(b'\x73\0\0\0')
        data.write_bytes(bytes(MAX_PROGRAM_BYTES - 4))
        self.assertFalse(check(self.root)['ok'])
        data.write_bytes(bytes(MAX_PROGRAM_BYTES - 5))
        self.assertTrue(check(self.root)['ok'])

    def test_image_symlink_is_rejected_before_reading(self):
        image = self.root / 'images/verify.code'
        image.unlink()
        image.symlink_to('/dev/zero')
        self.assertFalse(check(self.root)['ok'])

    def test_symlink_and_archive_file_are_rejected(self):
        (self.root / 'SigGolfCandidate' / 'Alias.lean').symlink_to('Helper.lean')
        (self.root / 'notes.zip').write_bytes(b'irrelevant')
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertGreaterEqual(len(value['errors']), 2)

    def test_signature_must_fit_memory_layout(self):
        self.claim['S'] = 16
        self.claim['layout']['signature'] = (1 << 24) - 8
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('signature buffer exceeds 16 MiB memory', value['errors'][0])

    def test_signature_size_is_capped(self):
        self.claim['S'] = 1 << 14
        self.claim['layout']['witness'] = 131168 + (1 << 14)
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.claim['S'] += 1
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the competition bounds', value['errors'][0])

    def test_cache_size_is_declared_and_capped(self):
        self.claim['K'] = 8
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])
        self.claim['K'] = (1 << 17) + 8
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('outside the competition bounds', value['errors'][0])

    def test_overlapping_buffers_are_rejected(self):
        self.claim['layout']['signature'] = 96
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('cache and signature buffers overlap', value['errors'][0])

    def test_unaligned_offset_is_rejected(self):
        self.claim['layout']['message'] = 1
        self.write_claim()
        value = check(self.root)
        self.assertFalse(value['ok'])
        self.assertIn('message offset is not 8-byte aligned', value['errors'][0])

    def test_empty_witness_may_share_an_address(self):
        self.claim['W'] = 0
        self.claim['layout']['witness'] = self.claim['layout']['cache']
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])

    def test_custom_layout_is_accepted(self):
        self.claim['layout'] = {'message': 0x40000, 'secret_key': 0x40100,
                                'public_key': 0x40200, 'cache': 0x80000,
                                'signature': 0x100000, 'witness': 0x100100}
        self.write_claim()
        value = check(self.root)
        self.assertTrue(value['ok'], value['errors'])


if __name__ == '__main__':
    unittest.main()
