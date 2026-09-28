import hashlib
import sys
import tempfile
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from verify import IMAGE_LIMIT, PROGRAMS, VerifyError, read_images


class ExtractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.folder = Path(self.temp.name)
        for name in PROGRAMS:
            (self.folder / f'{name}.code').write_bytes(b'')
            (self.folder / f'{name}.data').write_bytes(b'')
        (self.folder / 'keygen.code').write_bytes(bytes.fromhex('73000000 78563412'.replace(' ', '')))
        (self.folder / 'keygen.data').write_bytes(b'\xab\x01')

    def tearDown(self):
        self.temp.cleanup()

    def test_digests_and_sizes(self):
        images = read_images(self.folder)
        self.assertEqual(set(images), set(PROGRAMS))
        self.assertEqual(images['keygen']['code_words'], 2)
        self.assertEqual(images['keygen']['data_bytes'], 2)
        expected = hashlib.sha256((2).to_bytes(4, 'little') + bytes.fromhex('7300000078563412') + b'\xab\x01').hexdigest()
        self.assertEqual(images['keygen']['sha256'], expected)
        self.assertEqual(images['sign'], {'code_words': 0, 'data_bytes': 0,
                                          'sha256': hashlib.sha256(bytes(4)).hexdigest()})

    def test_missing_file_is_rejected(self):
        (self.folder / 'verify.data').unlink()
        with self.assertRaises(VerifyError):
            read_images(self.folder)

    def test_partial_word_is_rejected(self):
        (self.folder / 'sign.code').write_bytes(b'\x73\x00\x00')
        with self.assertRaises(VerifyError):
            read_images(self.folder)

    def test_oversized_image_is_rejected(self):
        (self.folder / 'expand.data').write_bytes(bytes(IMAGE_LIMIT))
        with self.assertRaises(VerifyError):
            read_images(self.folder)

    def test_symlink_is_rejected(self):
        (self.folder / 'expand.code').unlink()
        (self.folder / 'expand.code').symlink_to(self.folder / 'keygen.code')
        with self.assertRaises(VerifyError):
            read_images(self.folder)


if __name__ == '__main__':
    unittest.main()
