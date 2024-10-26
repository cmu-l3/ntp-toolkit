"""
Add packageName and importName to packages in lean_reservoir.json.

packageName is the package name of the Lean project (e.g. "mathlib").
importName is (one of the) import module name of the Lean project (e.g. "Mathlib").

They are extracted from the corresponding lakefiles at the commitVersion on GitHub.

Details:
* We are currently ignoring base modules other than the first one found (e.g. Counterexamples in Mathlib)
* The versions are not the "newest" version; they are the newest that can be built (by Lean Reservoir)
"""

import re

import requests
import pandas as pd

def analyze_lakefile_lean(lakefile_content):
    package_name_match = re.search(r"^package\s+(\S+)", lakefile_content, re.MULTILINE)
    import_name_match = re.search(r"^@\[default_target\]\s*lean_lib\s+(\S+)", lakefile_content, re.MULTILINE)
    if not import_name_match:
        import_name_match = re.search(r"^lean_lib\s+(\S+)", lakefile_content, re.MULTILINE)

    if package_name_match and import_name_match:
        package_name = package_name_match.group(1)
        import_name = import_name_match.group(1)
        return package_name, import_name
    else:
        raise ValueError("Required patterns not found in lakefile.lean")

def analyze_lakefile_toml(lakefile_content):
    package_name_match = re.search(r'^name\s*=\s*"([^"]+)"', lakefile_content, re.MULTILINE)
    import_name_match = re.search(r'^\[\[lean_lib\]\]\s*name\s*=\s*"([^"]+)"', lakefile_content, re.MULTILINE)

    if package_name_match and import_name_match:
        package_name = package_name_match.group(1)
        import_name = import_name_match.group(1)
        return package_name, import_name
    else:
        raise ValueError("Required patterns not found in lakefile.toml")

def analyze_lakefile(repo_url, commit_version="HEAD"):
    # try lakefile.toml and lakefile.lean
    lakefile_toml_url = f"{repo_url}/raw/{commit_version}/lakefile.toml"
    lakefile_lean_url = f"{repo_url}/raw/{commit_version}/lakefile.lean"

    response = requests.get(lakefile_toml_url)
    if response.status_code == 200:
        lakefile_toml_content = response.content.decode()
        return analyze_lakefile_toml(lakefile_toml_content)
    else:
        response = requests.get(lakefile_lean_url)
        if response.status_code == 200:
            lakefile_lean_content = response.content.decode()
            return analyze_lakefile_lean(lakefile_lean_content)
    raise RuntimeError(f"Failed to download lakefile from {lakefile_toml_url} and {lakefile_lean_url}")

if __name__ == "__main__":
    reservoir_json_file = "lean_reservoir.json"
    reservoir_dataframe = pd.read_json(reservoir_json_file)

    for index, row in reservoir_dataframe.iterrows():
        repo_url = row["repositoryURL"]
        commit_version = row["commitVersion"]
        try:
            package_name, import_name = analyze_lakefile(repo_url, commit_version)
            reservoir_dataframe.at[index, "packageName"] = package_name
            reservoir_dataframe.at[index, "importName"] = import_name
        except Exception as e:
            print(f"Error processing {repo_url} at {commit_version}: {e}")

    reservoir_dataframe.to_json(reservoir_json_file, orient="records")
