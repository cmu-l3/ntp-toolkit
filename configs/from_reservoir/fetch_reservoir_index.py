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
import toml


def analyze_lakefile_lean(lakefile_content) -> tuple[str, list[str]]:
    package_name_match = re.search(r"^package\s+(\S+)", lakefile_content, re.MULTILINE)
    # extract default lean_lib target names as import names
    import_name_match = list(re.finditer(r"^@\[default_target\]\s*lean_lib\s+(\S+)", lakefile_content, re.MULTILINE))
    if not import_name_match:
        # if none exist, extract the first lean_lib
        match = re.search(r"^lean_lib\s+(\S+)", lakefile_content, re.MULTILINE)
        if match:
            import_name_match = [match]

    if package_name_match and import_name_match:
        package_name = package_name_match.group(1)
        # in rare cases, the lakefile has a "globs" that asks to compile everything matching a glob
        # this misses many syntactic cases, but not many repositories use this so it is fine
        import_names = []
        for match in import_name_match:
            # for syntax, see Lake.Config.Glob; here we only process submodules (.+) (TODO)
            import_glob_match = re.search(r'^\s*\{\s*globs\s*:=\s*\#\[\s*\.submodules\s*\`([^\]\s]+)', lakefile_content[match.end(1):])
            if import_glob_match:
                import_names.append(f"glob:{import_glob_match.group(1)}.+")
            else:
                import_names.append(match.group(1))
        return package_name, import_names
    elif not package_name_match:
        raise ValueError("Package name not found in lakefile.lean")
    else:
        raise ValueError("Import name not found in lakefile.lean")

def analyze_lakefile_toml(lakefile_content) -> tuple[str, list[str]]:
    try:
        content = toml.loads(lakefile_content)
    except toml.TomlDecodeError:
        print("Bad lakefile.toml")
        raise

    if "name" in content and "lean_lib" in content and len(content["lean_lib"]) >= 1:
        package_name = content["name"]
        all_import_names = [lib["name"] for lib in content["lean_lib"] if "name" in lib]
        default_targets = [name for name in content.get("defaultTargets", []) if name in all_import_names]
        # extract default target names as import names; the first lean_lib if none exist
        if default_targets:
            targets = default_targets
        else:
            targets = [all_import_names[0]]
        import_names = []
        for lib in content["lean_lib"]:
            if "name" in lib and lib["name"] in targets:
                # in rare cases, the lakefile has a "globs" that asks to compile everything matching a glob
                if "globs" in lib:
                    for glob in lib["globs"]:
                        import_names.append(f"glob:{glob}")
                else:
                    import_names.append(lib["name"])
        return package_name, import_names
    elif "name" not in content:
        raise ValueError("Package name not found in lakefile.toml")
    else:
        raise ValueError("Import name not found in lakefile.toml")

def analyze_lakefile(repo_url, commit_version="HEAD") -> tuple[str, list[str]]:
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
            package_name, import_names = analyze_lakefile(repo_url, commit_version)
        except Exception as e:
            print(f"Error processing {repo_url} at {commit_version}: {e}")
            continue

        # We collect Init, Batteries, Mathlib training data separately
        if package_name in ["batteries", "mathlib"]:
            print(f"Skipping {package_name}")
            continue

        config_data = {
            "repo": repo_url,
            "commit": commit_version,
            "lean": toolchain_version,
            "name": package_name,
            "imports": import_names,
            "metadata": metadata,
        }

        # Hot fix: the specific commit for LeanCamCombi is broken on 2024-10-27; probably because of some git rebase/squash
        if repo_url == "https://github.com/YaelDillies/LeanCamCombi" and commit_version == "6fe1d16e9176584ebc45810385d7b1f29512caac":
            config_data["commit"] = "ef325f10fab9bfde5184048021dad23c94461e1d"
            config_data["lean"] = "leanprover/lean4:v4.13.0-rc3"

        safe_title = re.sub(r'[^a-zA-Z0-9_\-]', '--', metadata["fullName"])
        output_file = os.path.join(output_dir, f"{safe_title}.json")
        with open(output_file, "w") as f:
            json.dump(config_data, f, indent=4)

    with open("data.jsonl", "w") as f:
        for data in all_data:
            f.write(json.dumps(data))
            f.write("\n")
