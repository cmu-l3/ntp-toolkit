"""
Extract config JSONs from [Reservoir](https://reservoir.lean-lang.org/)

Details:
* We are currently ignoring base modules other than the first one found (e.g. ignoring Counterexamples in Mathlib)
* The extracted versions are not the newest version on GitHub; they are the newest that can be built (by Lean Reservoir)
* The repository information is from [reservoir-index](https://github.com/leanprover/reservoir-index)
* Some additional information is from lakefiles fetched from GitHub
"""

import json
import glob
import os
import re
import subprocess

import requests

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
    if os.path.isdir("reservoir-index"):
        print("Directory reservoir-index exists. Attempting to update:")
        subprocess.run(["git", "pull"], check=True, cwd="reservoir-index")
    else:
        subprocess.run(["git", "clone", "--depth=1", "https://github.com/leanprover/reservoir-index.git"], check=True)

    output_dir = "configs"
    os.makedirs(output_dir, exist_ok=True)
    all_data = []  # For logging purposes

    for project_dir in sorted(glob.glob("reservoir-index/*/*/")):
        print(f"Processing {project_dir}")
        builds_path = os.path.join(project_dir, "builds.json")
        metadata_path = os.path.join(project_dir, "metadata.json")
        if not (os.path.exists(builds_path) and os.path.exists(metadata_path)):
            continue
        with open(builds_path, "r") as builds_file:
            builds_data = json.load(builds_file)
        with open(metadata_path, "r") as metadata_file:
            metadata = json.load(metadata_file)

        source = metadata["sources"][0]  # why is this a list?
        repo_url = source["repoUrl"]

        # This is only for logging purposes
        data = {**source, **metadata}
        del data["sources"]
        all_data.append(data)

        # Search for the most recent version that built successfully
        if isinstance(builds_data, dict):
            builds = builds_data["data"]
        else:
            # In exceptional cases (perhaps legacy issues)
            builds = builds_data
        for build in builds:
            if "built" in build and build["built"]:
                most_recent_successful_build = build
                break
            # In exceptional cases (perhaps legacy issues)
            if "outcome" in build and build["outcome"] == "success":
                most_recent_successful_build = build
                break
        else:
            # No version was built successfully
            continue

        toolchain_version = most_recent_successful_build["toolchain"]
        commit_version = most_recent_successful_build["revision"]
        data.update(most_recent_successful_build)

        try:
            package_name, import_name = analyze_lakefile(repo_url, commit_version)
        except Exception as e:
            print(f"Error processing {repo_url} at {commit_version}: {e}")
            continue

        config_data = {
            "repo": repo_url,
            "commit": commit_version,
            "lean": toolchain_version,
            "name": package_name,
            "imports": [import_name],
            "metadata": metadata,
        }

        safe_title = re.sub(r'[^a-zA-Z0-9_\-]', '--', metadata["fullName"])
        output_file = os.path.join(output_dir, f"{safe_title}.json")
        with open(output_file, "w") as f:
            json.dump(config_data, f, indent=4)

    with open("data.jsonl", "w") as f:
        for data in all_data:
            f.write(json.dumps(data))
            f.write("\n")
