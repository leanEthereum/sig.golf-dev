#!/usr/bin/env python3
"""Exercise image binding with the pinned comparator (not a full scheme proof).

Run after `lake build SigGolf`; set COMPARATOR_BIN, COMPARATOR_LEAN4EXPORT,
and COMPARATOR_LANDRUN to the installed tools. Only these trusted fixtures run.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from images import PROGRAMS, render

ROOT = Path(__file__).resolve().parents[2]


def main():
    comparator = os.environ['COMPARATOR_BIN']
    config = json.loads((ROOT / 'verifier/comparator.json').read_text())
    # Isolate the new image and existing metric bindings. No fixture purports to
    # prove cryptographic security. The production config still requires certificate.
    config['theorem_names'].remove('SigGolf.Challenge.certificate')
    with tempfile.TemporaryDirectory(prefix='sig-image-binding-') as temp:
        project = Path(temp)
        for name in ('lean-toolchain', 'lakefile.lean', 'lake-manifest.json', 'SigGolf.lean'):
            shutil.copy2(ROOT / name, project / name)
        shutil.copytree(ROOT / 'SigGolf', project / 'SigGolf')
        (project / '.lake').mkdir()
        (project / '.lake/packages').symlink_to(ROOT / '.lake/packages', target_is_directory=True)
        for name in ('build', 'config'):
            shutil.copytree(ROOT / '.lake' / name, project / '.lake' / name)
        with (project / 'lakefile.lean').open('a') as stream:
            stream.write('\nlean_lib Solution\n')
        images = {name: (bytes.fromhex('9302100073000000'), b'\x01\x80\xff') for name in PROGRAMS}
        (project / 'SigGolf/Images.lean').write_text(render(images))
        challenge = (ROOT / 'verifier/Challenge.lean.in').read_text()
        for key, value in {'S': 8, 'W': 8, 'K': 0, 'C': 100, 'MESSAGE': 0, 'SECRET_KEY': 32,
                           'PUBLIC_KEY': 64, 'CACHE': 80, 'SIGNATURE': 80, 'WITNESS': 88}.items():
            challenge = challenge.replace('{{' + key + '}}', str(value))
        (project / 'SigGolf/Challenge.lean').write_text(challenge)
        (project / 'comparator.json').write_text(json.dumps(config))
        prefix = '''import SigGolf
import SigGolf.Images
namespace SigGolf.Challenge
example : SigGolf.Images.keygen.code = [0x00100293, 0x00000073] := rfl
example : SigGolf.Images.keygen.data = [1, 128, 255] := rfl
'''
        submission = '''noncomputable def submission : SigGolf.Submission :=
  { sizes := ⟨8, 8, 0⟩,
    layout := ⟨0, 32, 64, 80, 80, 88⟩,
    image := candidateImages }
'''
        metrics = '''theorem signature_bytes : submission.sizes.signature = 8 := rfl
theorem witness_bytes : submission.sizes.witness = 8 := rfl
theorem cache_bytes : submission.sizes.cache = 0 := rfl
theorem layout_offsets : submission.layout = ⟨0, 32, 64, 80, 80, 88⟩ := rfl
end SigGolf.Challenge
'''
        binding = 'theorem images_match : submission.image = SigGolf.Images.images := '
        cases = [
            ('literal', 'def candidateImages := SigGolf.Images.images\n', binding + 'rfl\n', True),
            ('choice_with_equality', '''noncomputable def candidateImages := Classical.choose
  (show ∃ f : SigGolf.Program → SigGolf.Riscv.Image, f = SigGolf.Images.images from ⟨_, rfl⟩)
''', binding + '''Classical.choose_spec
  (show ∃ f : SigGolf.Program → SigGolf.Riscv.Image, f = SigGolf.Images.images from ⟨_, rfl⟩)
''', True),
            ('native_implementation_is_not_authority', '''def nativeImages : SigGolf.Program → SigGolf.Riscv.Image := fun _ => ⟨[], []⟩
@[implemented_by nativeImages] def candidateImages := SigGolf.Images.images
''', binding + 'rfl\n', True),
            ('different_image', 'def candidateImages : SigGolf.Program → SigGolf.Riscv.Image := fun _ => ⟨[], []⟩\n',
             'theorem images_match : submission.image = candidateImages := rfl\n', False),
            ('axiom_equality', 'def candidateImages : SigGolf.Program → SigGolf.Riscv.Image := fun _ => ⟨[], []⟩\n',
             'axiom images_match : submission.image = SigGolf.Images.images\n', False),
            ('native_decide_equality', 'deriving instance DecidableEq for SigGolf.Riscv.Image\ndef candidateImages := SigGolf.Images.images\n',
             binding + 'by funext p; cases p <;> native_decide\n', False),
        ]
        for name, definitions, proof, accepted in cases:
            declaration = submission.replace('noncomputable def', 'def') if name == 'native_decide_equality' else submission
            (project / 'Solution.lean').write_text(prefix + definitions + declaration + proof + metrics)
            # Clean all fixture artifacts so Lake/comparator cannot reuse a prior case.
            for folder in (project / '.lake/build/lib/lean', project / '.lake/build/ir'):
                for pattern in ('Solution.*', 'SigGolf/Challenge.*', 'SigGolf/Images.*'):
                    for file in folder.glob(pattern):
                        file.unlink()
            process = subprocess.run(['lake', 'env', comparator, str(project / 'comparator.json')],
                                     cwd=project, capture_output=True, text=True, timeout=300)
            output = process.stdout + process.stderr
            if (process.returncode == 0 and 'Your solution is okay!' in output) != accepted:
                raise AssertionError(f'{name}: unexpected comparator result\n{output}')
            # Negative cases must reach comparison/axiom checking, not fail to compile.
            if output.count('Exporting #[SigGolf.Challenge.images_match') != 2 or ' from Solution' not in output:
                raise AssertionError(f'{name}: fixture did not reach export\n{output}')
            print(f'{name}: {"accepted" if accepted else "rejected"}', flush=True)


if __name__ == '__main__':
    main()
