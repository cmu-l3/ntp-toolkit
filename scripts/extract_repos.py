import argparse
import os
import subprocess
import json
from pathlib import Path


def _lakefile(repo, commit, name, cwd):
    contents = """import Lake
open Lake DSL

package «lean-training-data» {
  -- add any package configuration options here
}

require %s from git
  "%s.git" @ "%s"

require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "a34d3c1f7b72654c08abe5741d94794db40dbb2e"

@[default_target]
lean_lib TrainingData where

lean_lib Examples where

lean_exe training_data where
  root := `scripts.training_data

lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data

lean_exe state_comments where
  root := `scripts.state_comments

lean_exe premises where
  root := `scripts.premises

lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises

lean_exe declarations where
  root := `scripts.declarations

lean_exe all_modules where
  root := `scripts.all_modules

""" % (name, repo, commit)
    with open(os.path.join(cwd, 'lakefile.lean'), 'w') as f:
        f.write(contents)


def _examples(imports, cwd):
    contents = """
%s
""" % ('\n'.join(['import %s' % i for i in imports]))
    with open(os.path.join(cwd, 'Examples.lean'), 'w') as f:
        f.write(contents)

def _lean_toolchain(lean, cwd):
    contents = """%s""" % (lean)
    with open(os.path.join(cwd, 'lean-toolchain'), 'w') as f:
        f.write(contents)

def _setup(cwd):
    print("Building...")
    if Path(os.path.join(cwd, '.lake')).exists():
        subprocess.Popen(['rm -rf .lake'], shell=True).wait()
    if Path(os.path.join(cwd, 'lake-packages')).exists():
        subprocess.Popen(['rm -rf lake-packages'], shell=True).wait()
    if Path(os.path.join(cwd, 'lake-manifest.json')).exists():
        subprocess.Popen(['rm -rf lake-manifest.json'], shell=True).wait()
    subprocess.Popen(['lake update'], shell=True).wait()
    subprocess.Popen(['lake exe cache get'], shell=True).wait()
    subprocess.Popen(['lake build'], shell=True).wait()

def _import_file(name, import_file, old_version):
    name = name.replace('«', '').replace('»', '')
    if old_version:
        return os.path.join('lake-packages', name, import_file)
    else:
        return os.path.join('.lake', 'packages', name, import_file)

def _run(cwd, name, import_module, max_workers, flags):
    if max_workers is not None:
        flags.append('--max-workers')
        flags.append(str(max_workers))
    subprocess.run([
        'python3',
        '%s/scripts/run_pipeline.py' % cwd,
        '--output-base-dir', 'Examples/%s' % name.capitalize(),
        '--cwd', cwd,
        '--import-module', *import_module,
        *flags
    ], check=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--cwd', default='/Users/wellecks/projects/ntp-training-data/')
    parser.add_argument(
        '--config',
        default='configs/config.json',
        help='config file'
    )
    parser.add_argument(
        '--max-workers',
        default=None,
        type=int,
        help="maximum number of processes; defaults to number of processors"
    )
    parser.add_argument(
        '--skip_setup',
        action='store_true'
    )
    parser.add_argument(
        '--training_data',
        action='store_true'
    )
    parser.add_argument(
        '--full_proof_training_data',
        action='store_true'
    )
    parser.add_argument(
        '--premises',
        action='store_true'
    )
    parser.add_argument(
        '--state_comments',
        action='store_true'
    )
    parser.add_argument(
        '--full_proof_training_data_states',
        action='store_true'
    )
    parser.add_argument(
        '--training_data_with_premises',
        action='store_true'
    )
    parser.add_argument(
        '--declarations',
        action='store_true'
    )
    args = parser.parse_args()

    with open(args.config) as f:
        sources = json.load(f)

    flags = []
    if args.training_data:
        flags.append('--training_data')
    if args.full_proof_training_data:
        flags.append('--full_proof_training_data')
    if args.premises:
        flags.append('--premises')
    if args.state_comments:
        flags.append('--state_comments')
    if args.full_proof_training_data_states:
        flags.append('--full_proof_training_data_states')
    if args.training_data_with_premises:
        flags.append('--training_data_with_premises')
    if args.declarations:
        flags.append('--declarations')

    for source in sources:
        print("=== %s ===" % (source['name']))
        print(source)
        _lakefile(
            repo=source['repo'],
            commit=source['commit'],
            name=source['name'],
            cwd=args.cwd,
        )
        _examples(
            imports=source['imports'],
            cwd=args.cwd
        )
        _lean_toolchain(
            lean=source['lean'],
            cwd=args.cwd
        )
        if not args.skip_setup:
            _setup(
                cwd=args.cwd
            )
        _run(
            cwd=args.cwd,
            name=source['name'],
            import_module=source['imports'],
            # import_file=source['import_file'],
            # old_version=False if 'old_version' not in source else source['old_version'],
            max_workers=args.max_workers,
            flags=flags
        )
