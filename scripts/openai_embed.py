import json
import os
from typing import List, Dict, Tuple, Optional, Any, Literal

import tiktoken
from openai import OpenAI
import numpy as np
import tqdm


# Max number of simultaneous queries to OpenAI
BATCH_SIZE = 32
# See https://platform.openai.com/docs/guides/embeddings
EMBEDDING_SIZE = 3072
MAX_TOKENS = 8191

class Info():
    # Unique identifier
    name: str

    @classmethod
    def from_dict(cls, info: Dict[str, Any]):
        raise NotImplementedError

    def pretty_print(self) -> str:
        raise NotImplementedError

class Premise(Info):
    def __init__(
        self, kind: str, name: str, args: List[str],
        type: str, doc: Optional[str], line: Optional[int],
        module: str
    ):
        self.kind = kind
        self.name = name
        self.args = args
        self.type = type
        self.doc = doc
        self.line = line
        self.module = module

    @classmethod
    def from_dict(cls, info: Dict[str, Any]):
        return cls(
            kind=info["kind"],
            name=info["name"],
            args=info["args"],
            type=info["type"],
            doc=info["doc"],
            line=info["line"],
            module=info["module"],
        )

    def __repr__(self):
        return f"<Premise «{self.name}»>"

    def pretty_print(self):
        prettified = f"{self.kind} {self.name} {' '.join(self.args)} : {self.type}"
        if self.doc is not None:
            prettified = f"/-- {self.doc.strip()} -/\n{prettified}"
        return prettified

class State(Info):
    def __init__(
        self,
        state: str,
        next_tactic_explicit_constants: List[str],
        next_tactic_hammer_recommendation: List[str],
        hammer_recommendation_to_end_of_goal: List[str],
        next_tactic_is_simp_or_rw_variant: bool,
        next_tactic: str,
        source_up_to_tactic: Optional[str],
        module: str,
        pos_in_file: int,
        idx_in_file: int,
        line: int,
        decl: str
    ):
        self.state = state
        self.next_tactic_explicit_constants = next_tactic_explicit_constants
        self.next_tactic_hammer_recommendation = next_tactic_hammer_recommendation
        self.hammer_recommendation_to_end_of_goal = hammer_recommendation_to_end_of_goal
        self.next_tactic_is_simp_or_rw_variant = next_tactic_is_simp_or_rw_variant
        self.next_tactic = next_tactic
        self.source_up_to_tactic = source_up_to_tactic
        self.pos_in_file = pos_in_file
        self.idx_in_file = idx_in_file
        self.module = module
        self.line = line
        self.decl = decl

    @classmethod
    def from_dict(cls, info: Dict[str, Any]):
        return cls(
            state=info["state"],
            next_tactic_explicit_constants=info["nextTacticExplicitConstants"],
            next_tactic_hammer_recommendation=info["nextTacticHammerRecommendation"],
            hammer_recommendation_to_end_of_goal=info["hammerRecommendationToEndOfGoal"],
            next_tactic_is_simp_or_rw_variant=info["nextTacticIsSimpOrRwVariant"],
            next_tactic=info["nextTactic"],
            source_up_to_tactic=None,
            pos_in_file=info.get("posInFile", len(info["srcUpToTactic"])),
            idx_in_file=info.get("idxInFile", -1),
            decl=info["decl"],
            module=info["module"],
            line=info.get("posInFile", info["srcUpToTactic"].count("\n")),
        )

    @property
    def name(self):
        return f"{self.module}#{self.idx_in_file}"

    def __repr__(self):
        return f"<State {self.name}>"

    def pretty_print(self):
        return self.state

def openai_embed(client: OpenAI, texts: List[str], model: str = "text-embedding-3-large"):
    return np.array([
        response.embedding
        for response in client.embeddings.create(input=texts, model=model).data
    ], dtype=np.float32)

def num_tokens(text: str, encoding_name: str = "cl100k_base"):
    encoding = tiktoken.get_encoding(encoding_name)
    return len(encoding.encode(text))

def get_info(info_type: Literal["premise", "state"]) -> Tuple[List[Info], Dict[str, int]]:
    infos = []
    name2idx = {}
    infos_dir = {
        "premise": "Examples/Mathlib/Declarations",
        "state": "Examples/Mathlib/TrainingDataWithPremises",
    }[info_type]
    info_cls = {
        "premise": Premise,
        "state": State,
    }[info_type]
    for json_file in sorted(os.listdir(infos_dir)):
        if json_file.endswith(".jsonl"):
            with open(os.path.join(infos_dir, json_file)) as f:
                for i, line in enumerate(f):
                    info_dict = json.loads(line)
                    info: Info = info_cls.from_dict({
                        **info_dict,
                        "module": json_file.removesuffix(".jsonl"),
                        "idxInFile": i,
                    })
                    if info.name in name2idx:
                        raise ValueError(f"Found duplicate {info}")
                    name2idx[info.name] = len(infos)
                    infos.append(info)
    return infos, name2idx

def get_premises() -> Tuple[List[Premise], Dict[str, int]]:
    return get_info("premise") # type: ignore

def get_states() -> Tuple[List[State], Dict[str, int]]:
    return get_info("state") # type: ignore

def embed_infos(client: OpenAI, info_type: Literal["premise", "state"]):
    infos, _ = get_info(info_type)

    # This removes 4 states from entire mathlib, so should be fine
    infos = [
        info for info in infos
        if num_tokens(info.pretty_print()) <= MAX_TOKENS
    ]

    print(f"Embedding {len(infos)} {info_type}s")

    os.makedirs("embeddings", exist_ok=True)

    for i in tqdm.trange(0, len(infos), BATCH_SIZE):
        save_file = f"embeddings/{info_type}_batch_{i}-{i + BATCH_SIZE}.npz"
        if os.path.isfile(save_file):
            continue
        batch_infos = infos[i : i + BATCH_SIZE]
        batch_names = [info.name for info in batch_infos]
        batch_embeddings = openai_embed(
            client,
            [info.pretty_print() for info in batch_infos]
        )
        np.savez(save_file, names=batch_names, embeddings=batch_embeddings)

    if not os.path.isfile(f"embeddings/{info_type}_embeddings.npz"):
        print("Collating results")
        names = []
        embeddings = np.zeros((len(infos), EMBEDDING_SIZE), dtype=np.float32)
        for i in tqdm.trange(0, len(infos), BATCH_SIZE):
            save_file = f"embeddings/{info_type}_batch_{i}-{i + BATCH_SIZE}.npz"
            batch = np.load(save_file)
            names.extend(batch["names"])
            embeddings[i : i + BATCH_SIZE] = batch["embeddings"]
        np.savez(f"embeddings/{info_type}_embeddings.npz", names=names, embeddings=embeddings)

    print(f"Saved to embeddings/{info_type}_embeddings.npz")

def get_premise_embeddings():
    premises, name2idx = get_premises()
    embeddings_info = np.load("embeddings/premise_embeddings.npz")
    embeddings = embeddings_info["embeddings"]
    names = embeddings_info["names"]
    premises = [premises[name2idx[name]] for name in names]
    return premises, embeddings

def get_state_embeddings():
    states, name2idx = get_states()
    embeddings_info = np.load("embeddings/state_embeddings.npz")
    embeddings = embeddings_info["embeddings"]
    names = embeddings_info["names"]
    states = [states[name2idx[name]] for name in names]
    return states, embeddings

def retrieve(query_embeddings: np.ndarray, key_embeddings: np.ndarray) -> Tuple[np.ndarray, np.ndarray]:
    """Retrieve closest embeddings to a given queries.
    
    Args:
        query_embeddings: (num_queries, embedding_size) array
        key_embeddings: (num_keys, embedding_size) array

    Returns:
        scores (num_queries, num_keys) and indices (num_queries, num_keys) of keys closest to queries in dot product (sorted descending)
    """
    # Note: embeddings returned by OpenAI are already normalized, so dot product = cosine similarity
    scores = np.dot(query_embeddings, key_embeddings.T)  # (num_queries, num_keys)
    sorted_indices = np.argsort(-scores, axis=1)  # (num_queries, num_keys)
    sorted_scores = np.take_along_axis(scores, sorted_indices, axis=1)  # (num_queries, num_keys)
    return sorted_scores, sorted_indices

def eval_retrieval(
    batch_size: int = 1024,
    maxlogk: int = 10,
    retrieve_for: Literal["hammer", "next_tactic", "simp_or_rw"] = "hammer"
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    premises, premise_embeddings = get_premise_embeddings()
    states, state_embeddings = get_state_embeddings()
    if retrieve_for == "simp_or_rw":
        state_embeddings = state_embeddings[[state.next_tactic_is_simp_or_rw_variant for state in states]]
        states = [state for state in states if state.next_tactic_is_simp_or_rw_variant]
    with open("Examples/Mathlib/Imports.jsonl") as f:
        module_names: List[str] = json.load(f)
    premise_module_idxs = [module_names.index(premise.module) for premise in premises]
    state_module_idxs = [module_names.index(state.module) for state in states]
    premise_name2idx = {premise.name: i for i, premise in enumerate(premises)}
    # state_name2idx = {state.name: i for i, state in enumerate(states)}
    precisions = np.zeros((len(states), maxlogk + 1), dtype=np.float32)
    recalls = np.zeros((len(states), maxlogk + 1), dtype=np.float32)
    f1s = np.zeros((len(states), maxlogk + 1), dtype=np.float32)
    for i in tqdm.trange(0, len(states), batch_size):
        scores, indices = retrieve(state_embeddings[i : i + batch_size], premise_embeddings)
        for state_idx, (state, retrieved_indices_all) in enumerate(zip(states[i : i + batch_size], indices), i):
            # Take the top k retrieved premises
            retrieved_indices = []
            for j in retrieved_indices_all:
                # Restrict to premises visible to state
                if (premise_module_idxs[j], premises[j].line or 0) <= (state_module_idxs[state_idx], state.line):
                    retrieved_indices.append(j)
                if len(retrieved_indices) >= 2 ** maxlogk:
                    break

            # Determine the set of relevant premises
            if retrieve_for == "hammer":
                relevant_names = state.hammer_recommendation_to_end_of_goal
            elif retrieve_for == "simp_or_rw" or retrieve_for == "next_tactic":
                relevant_names = state.next_tactic_explicit_constants
            # Restrict to existing premises (i.e. in Mathlib)
            relevant_indices = {premise_name2idx[name] for name in relevant_names if name in premise_name2idx}

            # Whether each retrieved premise is relevant
            retrieved_is_relevant = np.array([i in relevant_indices for i in retrieved_indices])

            # Calculate metrics for reach k
            for logk in range(0, maxlogk + 1):
                k = 2 ** logk
                num_retrieved_relevant = retrieved_is_relevant[:k].sum()
                precision = num_retrieved_relevant / k
                if len(relevant_indices) == 0:
                    recall = 1.0  # corner case
                else:
                    recall = num_retrieved_relevant / len(relevant_indices)
                if num_retrieved_relevant == 0:
                    f1 = 0.0  # corner case
                else:
                    f1 = 2 * precision * recall / (precision + recall)
                precisions[state_idx, logk] = precision
                recalls[state_idx, logk] = recall
                f1s[state_idx, logk] = f1
    return precisions, recalls, f1s

# TODO merge with eval_retrieval
def eval_bm25_retrieval(
    batch_size: int = 1024,
    maxlogk: int = 10,
    retrieve_for: Literal["hammer", "next_tactic", "simp_or_rw"] = "hammer"
) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    import bm25s
    from transformers import AutoTokenizer

    premises, premise_embeddings = get_premise_embeddings()
    states, state_embeddings = get_state_embeddings()
    del premise_embeddings, state_embeddings  # don't need

    if retrieve_for == "simp_or_rw":
        states = [state for state in states if state.next_tactic_is_simp_or_rw_variant]
    with open("Examples/Mathlib/imports.jsonl") as f:
        module_names: List[str] = [json.loads(line) for line in f]
    premise_module_idxs = [module_names.index(premise.module) for premise in premises]
    state_module_idxs = [module_names.index(state.module) for state in states]
    premise_name2idx = {premise.name: i for i, premise in enumerate(premises)}
    # state_name2idx = {state.name: i for i, state in enumerate(states)}
    precisions = np.zeros((len(states), maxlogk + 1), dtype=np.float32)
    recalls = np.zeros((len(states), maxlogk + 1), dtype=np.float32)
    f1s = np.zeros((len(states), maxlogk + 1), dtype=np.float32)

    # Build BM25
    tokenizer = AutoTokenizer.from_pretrained("hf-internal-testing/llama-tokenizer", use_fast=True)
    retriever = bm25s.BM25()
    retriever.index([tokenizer.tokenize(premise.pretty_print()) for premise in premises])

    for i in tqdm.trange(0, len(states), batch_size):
        # Retrieve using BM25
        indices, scores = retriever.retrieve(
            [tokenizer.tokenize(state.pretty_print()) for state in states[i : i + batch_size]],
            k=len(premises)
        )

        for state_idx, (state, retrieved_indices_all) in enumerate(zip(states[i : i + batch_size], indices), i):
            # Take the top k retrieved premises
            retrieved_indices = []
            for j in retrieved_indices_all:
                # Restrict to premises visible to state
                if (premise_module_idxs[j], premises[j].line or 0) <= (state_module_idxs[state_idx], state.line):
                    retrieved_indices.append(j)
                if len(retrieved_indices) >= 2 ** maxlogk:
                    break

            # Determine the set of relevant premises
            if retrieve_for == "hammer":
                relevant_names = state.hammer_recommendation_to_end_of_goal
            elif retrieve_for == "simp_or_rw" or retrieve_for == "next_tactic":
                relevant_names = state.next_tactic_explicit_constants
            # Restrict to existing premises (i.e. in Mathlib)
            relevant_indices = {premise_name2idx[name] for name in relevant_names if name in premise_name2idx}

            # Whether each retrieved premise is relevant
            retrieved_is_relevant = np.array([i in relevant_indices for i in retrieved_indices])

            # Calculate metrics for reach k
            for logk in range(0, maxlogk + 1):
                k = 2 ** logk
                num_retrieved_relevant = retrieved_is_relevant[:k].sum()
                precision = num_retrieved_relevant / k
                if len(relevant_indices) == 0:
                    recall = 1.0  # corner case
                else:
                    recall = num_retrieved_relevant / len(relevant_indices)
                if num_retrieved_relevant == 0:
                    f1 = 0.0  # corner case
                else:
                    f1 = 2 * precision * recall / (precision + recall)
                precisions[state_idx, logk] = precision
                recalls[state_idx, logk] = recall
                f1s[state_idx, logk] = f1
    return precisions, recalls, f1s

def plot_retrieval(precisions, recalls, f1s):
    import matplotlib.pyplot as plt
    plt.xscale("log")
    plt.xlabel("$k$ retrieved premises")
    plt.ylim((0, 1))
    ks = 2 ** np.arange(precisions.shape[1])
    def plot(series, color, label):
        mean = np.mean(series, axis=0)
        lower, upper = np.quantile(series, [.25, .75], axis=0)
        plt.plot(ks, mean, f"{color}-", label=label)
        plt.fill_between(ks, lower, upper, color=color, alpha=0.2)
    plot(precisions, "C0", "Precision@$k$")
    plot(recalls, "C1", "Recall@$k$")
    plot(f1s, "C2", "F1@$k$")
    plt.legend(loc="upper left")
    plt.savefig("embeddings/eval_openai_retrieval.pdf")
    plt.show()

def plot_recall_by_module(states: List[State], recalls):
    import matplotlib.pyplot as plt
    logk = 8
    assert len(states) == recalls.shape[0]
    modules = [s.module for s in states]
    uniq_modules = np.array(sorted({
        m.split(".")[1] for m in modules
    }))
    recalls_by_module = np.array([
        np.mean(recalls[[m.split(".")[1] == module for m in modules], logk])
        for module in uniq_modules
    ])
    sorting = recalls_by_module.argsort()
    plt.barh(uniq_modules[sorting], recalls_by_module[sorting])
    plt.xlabel(f"Recall@{2 ** logk}")
    plt.xlim((0, 1))
    plt.ylabel("Mathlib module")
    plt.savefig("embeddings/eval_openai_retrieval_by_module.pdf")
    plt.show()

client = OpenAI()
