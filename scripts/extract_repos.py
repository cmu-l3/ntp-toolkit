import argparse
import glob
import os
import subprocess
import json
from pathlib import Path


# TODO: only add necessary lean_exe into lakefile.lean
doc_gen = """
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4.git" @ "%s"
"""

def _lakefile(repo, commit, name, cwd, require_doc_gen=False, toolchain_version="main"):
    contents = """import Lake
open Lake DSL

package «lean-training-data» {
  moreLeanArgs := #[
    "-Dlinter.unusedVariables=false",
    -- for supporting more lean versions, some usages in the code are deprecated
    -- a macro TODO is to make the code more future proof (e.g. name change of HashMap)
    "-Dlinter.deprecated=false"
  ]
}

require leanPremiseSelection from git
  "https://github.com/JOSHCLUNE/lean-premise-selection.git" @ "86f02182e5b30737b41aae20b8ef59d3f03d0a84"

require QuerySMT from git
  "https://github.com/JOSHCLUNE/LeanSMTParser.git" @ "15c641b2f5330aef1451e97d1c5fcf7ad584ffcf"

require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "v4.18.0"

require %s from git
  "%s.git" @ "%s"

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

@[default_target]
lean_exe add_premises where
  root := `scripts.add_premises
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

def _lake_update(cwd):
    if Path(os.path.join(cwd, '.lake')).exists():
        subprocess.run(['rm', '-rf', '.lake'], cwd=cwd, check=True)
    if Path(os.path.join(cwd, 'lake-packages')).exists():
        subprocess.run(['rm', '-rf', 'lake-packages'], cwd=cwd, check=True)
    if Path(os.path.join(cwd, 'lake-manifest.json')).exists():
        subprocess.run(['rm', '-rf', 'lake-manifest.json'], cwd=cwd, check=True)
    print("Running lake udpate ...")
    subprocess.run(['lake', 'update'], check=True)

def _lake_build(cwd):
    print("Building...")
    # this depends on mathlib; if the package does not require mathlib it will fail
    try:
        subprocess.run(['lake', 'exe', 'cache', 'get'], cwd=cwd, check=True)
    except subprocess.CalledProcessError:
        print("'lake exe cache get' command failed. This is probably because mathlib is not a dependency. Continuing...")
    subprocess.run(['lake', 'build'], cwd=cwd, check=True)

def _get_imports(cwd, name, imports: list[str]) -> list[str]:
    import_modules = []
    for module in imports:
        # The lakefile can (*very rarely*) specify a glob pattern
        # The "glob:" prefix is user-added in the config (or see fetch_reservoir_index.py)
        if module.startswith("glob:"):
            pattern = module.removeprefix("glob:")
            # See Lake.Config.Glob
            if not pattern.endswith("+"):
                import_modules.append(pattern)
                continue
            elif pattern.endswith(".+"):
                pattern = pattern.removesuffix(".+") + "/**/*.lean"
            elif pattern.endswith(".*"):
                import_modules.append(pattern.removesuffix(".*"))
                pattern = pattern.removesuffix(".*") + "/**/*.lean"
            root_dir = os.path.join(cwd, ".lake", "packages", _unescape_lean_name(name))
            print(pattern, root_dir)
            for import_file_path in glob.glob(pattern, root_dir=root_dir, recursive=True):
                import_modules.append(import_file_path.removesuffix(".lean").replace(os.path.sep, "."))
        else:
            import_modules.append(module)
    print(f"All import modules: {import_modules}")
    return import_modules

def _unescape_lean_name(name: str):
    name = name.replace('«', '').replace('»', '')
    return name

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
        '--output-base-dir', os.path.join('Examples', _unescape_lean_name(name)),
        '--cwd', cwd,
        '--import-module', *import_module,
        '--name', _unescape_lean_name(name),
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
        '--skip_existing',
        action='store_true',
        help='Do not overwrite existing output .jsonl files'
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
    parser.add_argument(
        '--convert_minictx',
        action='store_true'
    )
    args = parser.parse_args()

    with open(args.config) as f:
        sources = json.load(f)
        if not isinstance(sources, list):
            sources = [sources]

    flags = ['--task']
    if args.training_data:
        flags.append('training_data')
    if args.full_proof_training_data:
        flags.append('full_proof_training_data')
    if args.premises:
        flags.append('premises')
    if args.state_comments:
        flags.append('state_comments')
    if args.full_proof_training_data_states:
        flags.append('full_proof_training_data_states')
    if args.training_data_with_premises:
        flags.append('--training_data_with_premises')
    if args.add_imports:
        flags.append('--add_imports')
    if args.declarations:
        flags.append('declarations')
    if args.imports:
        flags.append('imports')
    if args.convert_minictx:
        flags.append('convert_minictx')

    for source in sources:
        print("=== %s ===" % (source['repo']))
        print(source)
        if not args.skip_setup:
            _lean_toolchain(
                lean=source['lean'],
                cwd=args.cwd
            )
            _lakefile(
                repo=source['repo'],
                commit=source['commit'],
                name=source['name'],
                cwd=args.cwd,
                # extracting declarations require doc-gen4
                require_doc_gen=args.declarations,
                toolchain_version=source['lean'].removeprefix('leanprover/lean4:')
            )
            _lake_update(
                cwd=args.cwd
            )
            imports = _get_imports(args.cwd, source['name'], source['imports'])
            _examples(
                imports=imports,
                cwd=args.cwd
            )
            _lake_build(
                cwd=args.cwd
            )
        else:
            imports = _get_imports(args.cwd, source['name'], source['imports'])
        _run(
            cwd=args.cwd,
            name=source['name'],
            import_module=imports,
            # import_file=source['import_file'],
            # old_version=False if 'old_version' not in source else source['old_version'],
            max_workers=args.max_workers,
            flags=flags
        )
