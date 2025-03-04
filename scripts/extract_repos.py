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

require QuerySMT from git
  "https://github.com/JOSHCLUNE/LeanSMTParser.git" @ "842ca2a4a780f1a3589c930ef82ebb08368682f7"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.16.0"

@[default_target]
lean_lib TrainingData where

lean_lib temp where

lean_lib Examples where

lean_exe training_data where
  root := `scripts.training_data
  supportInterpreter := true

lean_exe full_proof_training_data where
  root := `scripts.full_proof_training_data
  supportInterpreter := true

lean_exe state_comments where
  root := `scripts.state_comments
  supportInterpreter := true

lean_exe premises where
  root := `scripts.premises
  supportInterpreter := true

@[default_target]
lean_exe training_data_with_premises where
  root := `scripts.training_data_with_premises
  supportInterpreter := true

@[default_target]
lean_exe tactic_benchmark where
  root := `scripts.tactic_benchmark
  supportInterpreter := true

@[default_target]
lean_exe add_imports where
  root := `scripts.add_imports
  supportInterpreter := true

lean_exe all_modules where
  root := `scripts.all_modules
  supportInterpreter := true

@[default_target]
lean_exe declarations where
  root := `scripts.declarations
  supportInterpreter := true

@[default_target]
lean_exe imports where
  root := `scripts.imports
  supportInterpreter := true

@[default_target]
lean_exe update_hammer_blacklist where
  root := `scripts.update_hammer_blacklist
  supportInterpreter := true
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
        subprocess.run(['rm', '-rf', '.lake'], check=True)
    if Path(os.path.join(cwd, 'lake-packages')).exists():
        subprocess.run(['rm', '-rf', 'lake-packages'], check=True)
    if Path(os.path.join(cwd, 'lake-manifest.json')).exists():
        subprocess.run(['rm', '-rf', 'lake-manifest.json'], check=True)
    subprocess.run(['lake', 'update'], check=True)
    subprocess.run(['lake', 'exe', 'cache', 'get'], check=True)
    subprocess.run(['lake', 'build'], check=True)

# def _import_file(name, import_file, old_version):
#     name = name.replace('«', '').replace('»', '')
#     if old_version:
#         return os.path.join('lake-packages', name, import_file)
#     else:
#         return os.path.join('.lake', 'packages', name, import_file)

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
        '--add_imports',
        action='store_true'
    )
    parser.add_argument(    
        '--declarations',
        action='store_true'
    )
    parser.add_argument(
        '--imports',
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
    if args.add_imports:
        flags.append('--add_imports')
    if args.declarations:
        flags.append('--declarations')
    if args.imports:
        flags.append('--imports')

    for source in sources:
        print("=== %s ===" % (source['name']))
        print(source)
        _lakefile(
            repo=source['repo'],
            commit=source['commit'],
            name=source['name'],
            cwd=args.cwd
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
