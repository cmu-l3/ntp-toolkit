import argparse
import json
import os
from packaging import version

from extract_repos import _unescape_lean_name


MIN_LEAN4_VERSION = "4.8.0-rc1"  # we rely on the Std -> Batteries name change
MIN_LEAN4_NIGHTLY_VERSION = (2024, 5, 2)  # this is the date of 4.8.0-rc1

def check_lean_version(lean_version_str: str):
    lean_version_str = lean_version_str.removeprefix("leanprover/lean4:")

    # Handle the cases of nightly lean4 versions
    if lean_version_str.startswith("nightly-"):  # nightly-YYYY-MM-DD
        _, year, month, date = lean_version_str.split("-")
        if (int(year), int(month), int(date)) >= MIN_LEAN4_NIGHTLY_VERSION:
            return True
        else:
            return False

    # Incidentally, the version string used by lean4 conforms to the PEP 440 standard
    # so we use a package that parses versions for PEP 440 (packaging.version).
    # This handles cases like rc as well.
    lean_version = version.parse(lean_version_str)
    if lean_version >= version.parse(MIN_LEAN4_VERSION):
        return True
    else:
        return False

def already_extracted(name: str, cwd: str) -> bool:
    out_dir = os.path.join(cwd, 'Examples', _unescape_lean_name(name))
    return os.path.exists(out_dir)

def check_config(config_file: str, cwd: str) -> tuple[bool, bool, str]:
    with open(config_file, "r") as file:
        config = json.load(file)
        # This only supports when the config is a single dict
        assert isinstance(config, dict)

    lean_version_str = config["lean"]
    valid = True
    should_extract = True
    if not check_lean_version(lean_version_str):
        valid = False

    if already_extracted(config["name"], cwd):
        should_extract = False

    return (valid, should_extract, lean_version_str)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Check Lean version in config file.")
    parser.add_argument("config_file", type=str, help="Path to the config JSON file")
    parser.add_argument("--cwd", type=str, help="Path to ntp-toolkit")
    args = parser.parse_args()

    valid, should_extract, lean_version_str = check_config(args.config_file, args.cwd)
    if not valid:
        raise ValueError(f"Lean version {lean_version_str} is less than minimum required by ntp-toolkit ({MIN_LEAN4_VERSION})")
    if not should_extract:
        raise ValueError("Shouldn't extract (already extracted)")
