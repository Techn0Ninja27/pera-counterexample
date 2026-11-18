"""Rationally specified PERA and genuine rank-two LoRA controls."""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
from fractions import Fraction
from pathlib import Path
import torch

HERE = Path(__file__).resolve().parent
PROTOCOL = HERE / "protocol-v2.json"


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def frac(value):
    return Fraction(value) if isinstance(value, int) else Fraction(value)


def matmul(left, right):
    return [[sum(left[i][k] * right[k][j] for k in range(len(right))) for j in range(len(right[0]))] for i in range(len(left))]


def check(output: Path) -> dict:
    if output.exists():
        raise FileExistsError("refusing to overwrite an existing result")
    protocol = json.loads(PROTOCOL.read_text())
    if platform.python_version() != protocol["environment"]["python"] or torch.__version__ != protocol["environment"]["torch"]:
        raise RuntimeError("environment differs from frozen protocol")
    a = [[Fraction(1)], [Fraction(-1)], [Fraction(0)]]
    b = [[Fraction(1, 2)], [Fraction(-1, 2)], [Fraction(0)]]
    h = Fraction(2)
    linear = matmul(b, [[x[0] for x in a]])
    b2 = [[x[0] * x[0]] for x in b]
    a2 = [[x[0] * x[0] for x in a]]
    pera = [[linear[i][j] + h * b2[i][0] * a2[0][j] for j in range(3)] for i in range(3)]
    target = [[Fraction(2, 3), Fraction(-1, 3), Fraction(-1, 3)], [Fraction(-1, 3), Fraction(2, 3), Fraction(-1, 3)], [Fraction(-1, 3), Fraction(-1, 3), Fraction(2, 3)]]
    B = [[Fraction(x) for x in row] for row in protocol["lora_rank_two_factorization"]["B"]]
    A = [[Fraction(x) for x in row] for row in protocol["lora_rank_two_factorization"]["A"]]
    lora2 = matmul(B, A)
    checks = {
        "pera_exact_rational_diag": pera == [[Fraction(1), Fraction(0), Fraction(0)], [Fraction(0), Fraction(1), Fraction(0)], [Fraction(0), Fraction(0), Fraction(0)]],
        "target_exact_projector": matmul(target, target) == target,
        "rank_two_lora_exact_rational": lora2 == target,
        "parameter_count_derived": (sum(len(row) for row in b) + sum(len(row) for row in a) + 1) == 7 and sum(len(row) for row in B) + sum(len(row) for row in A) == 12,
    }
    torch.set_default_dtype(torch.float64)
    target_t = torch.tensor([[float(x) for x in row] for row in target])
    pera_t = torch.tensor([[float(x) for x in row] for row in pera])
    lora1_t = torch.tensor([[float(x) for x in row] for row in linear])
    lora2_t = torch.tensor([[float(x) for x in row] for row in lora2])
    errors = {"lora_rank_1": float(torch.linalg.matrix_norm(target_t - lora1_t, ord=2)), "pera_rank_1": float(torch.linalg.matrix_norm(target_t - pera_t, ord=2)), "lora_rank_2": float(torch.linalg.matrix_norm(target_t - lora2_t, ord=2))}
    checks.update({"lora_rank_one_error_one": abs(errors["lora_rank_1"] - 1) < 1e-14, "pera_error_sqrt_two_thirds": abs(errors["pera_rank_1"] - (2 / 3) ** 0.5) < 1e-14, "lora_rank_two_error_zero": errors["lora_rank_2"] < 1e-14})
    result = {"schema": "pera-usefulness-check-result.v2", "status": "completed" if all(checks.values()) else "checks_failed", "protocol_sha256": sha(PROTOCOL), "runner_sha256": sha(Path(__file__).resolve()), "environment": {"python": platform.python_version(), "torch": torch.__version__, "dtype": "float64", "device": "cpu"}, "exact": {"target": target, "pera_rank_1": pera, "lora_rank_2": lora2}, "spectral_errors": errors, "parameter_counts": {"lora_rank_1": 6, "pera_rank_1": 7, "lora_rank_2": 12}, "proven_lower_bound": 1 / (3 ** 0.5), "checks": checks, "limitations": ["One hand-constructed 3x3 target.", "No optimizer or transformer task benchmark.", "PERA optimum is bounded between 1/sqrt(3) and sqrt(2/3); this construction is not claimed optimal.", "Counts cover factor and coefficient tensors only."], "novelty_established": False, "task_usefulness_established": False}
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(result, indent=2, default=str) + "\n")
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = check(args.output)
    print(json.dumps({"status": result["status"], "output": str(args.output), "checks": result["checks"]}))
