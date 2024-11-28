# TODO:
# 1. rename to should extract.py
# 2. if already extracted, skip
# 3. if has no mathlib dependency, skip

import argparse
import json
from packaging import version


MIN_LEAN4_VERSION = "4.8.0-rc1"  # we rely on the Std -> Batteries name change
MIN_LEAN4_NIGHTLY_VERSION = (2024, 5, 2)  # this is the date of 4.8.0-rc1

def check_lean_version(config_file) -> tuple[bool, str]:
    # TODO: this only supports when the config is a single dict
    with open(config_file, "r") as file:
        config = json.load(file)

    lean_version_str: str = config["lean"]
    lean_version_str = lean_version_str.removeprefix("leanprover/lean4:")

    # Handle the cases of nightly lean4 versions
    if lean_version_str.startswith("nightly-"):  # nightly-YYYY-MM-DD
        _, year, month, date = lean_version_str.split("-")
        if (int(year), int(month), int(date)) >= MIN_LEAN4_NIGHTLY_VERSION:
            return (True, lean_version_str)
        else:
            return (False, lean_version_str)

    # Incidentally, the version string used by lean4 conforms to the PEP 440 standard
    # so we use a package that parses versions for PEP 440 (packaging.version).
    # This handles cases like rc as well.
    lean_version = version.parse(lean_version_str)
    if lean_version >= version.parse(MIN_LEAN4_VERSION):
        return (True, lean_version_str)
    else:
        return (False, lean_version_str)

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Check Lean version in config file.")
    parser.add_argument("config_file", type=str, help="Path to the config JSON file")
    args = parser.parse_args()

    valid, lean_version_str = check_lean_version(args.config_file)
    if not valid:
        raise ValueError(f"Lean version {lean_version_str} is less than minimum required by ntp-toolkit ({MIN_LEAN4_VERSION})")
