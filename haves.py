import json

data_path = "test.jsonl"

with open(data_path) as f:
    theorems = [json.loads(l) for l in f]

def skip_tactic(tactic: dict[str, str]) -> bool:
    next_tactic = tactic["nextTactic"]
    if next_tactic.startswith("intro"):
        return True
    if next_tactic.startswith("have"):
        # the state preceding the `have` is not modified anyway
        return True
    return False

for theorem in theorems:
    name = theorem["declName"]
    tactics = theorem["tactics"]
    # Determine declaration
    for tactic in tactics:
        if tactic["decl"]:
            decl = tactic["decl"]
            break
    else:
        decl = "<<couldn't determine decl>>"

    # get progressive, deduplicated tactic states
    state_signatures = []
    for tactic in tactics:
        if skip_tactic(tactic):
            continue
        for state_signature in tactic["statesAsSignatures"]:
            if state_signature not in state_signatures:
                state_signatures.append(state_signature)

    haves = []
    i = 1
    # The natural order of haves is reverse of the order of tactic states
    for state_signature in state_signatures[::-1]:
        have = state_signature.replace("extracted", f"have h{i}", 1)
        haves.append("  " + have.replace("\n", "\n  ") + " := by sorry")
        i += 1

    print(decl + ":= by")
    for have in haves:
        print(have)
    print(f"  exact h{i - 1}")
    print()
