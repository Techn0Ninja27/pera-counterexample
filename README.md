# PERA approximation-bound counterexample

A small, independently checked correction concerning Appendix A.3, Theorem 1
of [PERA (Findings of ACL 2026)](https://aclanthology.org/2026.findings-acl.650.pdf).
This is an independent verification repository, not the authors’ implementation.

**[Read the technical note](docs/technical-note.md)** ·
**[Verification receipt](verification/result.json)** ·
**[Axiom audit](verification/axioms.log)**

For the real rank-one-base update

$$
M=ba^T+h(b\odot b)(a\odot a)^T,
\qquad P=I-\mathbf1\mathbf1^T/3\in\mathbb R^{3\times3},
$$

Lean proves that P has rank two and that **every** choice of real a, b and h
satisfies spectral error `||P-M||₂ ≥ 1/√3`, including the infimum. The source
bound would require zero error for this target. The project uses mathlib’s
Euclidean operator norm, not a different matrix norm.

There is also a positive result: an explicit PERA witness has error at most
`√(2/3) < 1`, while every rank-one LoRA update has error at least 1 on this
target. This is a bounded algebraic comparison, not a downstream model benchmark.

## Inspect without running anything

- [Short report and proposed correction](docs/technical-note.md)
- [Exact source-claim scope](docs/claim-scope.md)
- [Independent formalization audit](docs/independent-formal-audit.md)
- [Prior-publication check](docs/prior-check.md)
- [Core Lean theorem](PeraVerification/Counterexample.lean)
- [Rank-two premise and refutation](PeraVerification/TargetProperties.lean)
- [Constructive bound](PeraVerification/Usefulness.lean) and [LoRA comparison](PeraVerification/LoRAComparison.lean)
- [Author contact](docs/contact.md)

## Reproduce the verification

Install [Lean/Elan](https://lean-lang.org/install/manual/), then:

```sh
git clone https://github.com/Techn0Ninja27/pera-counterexample.git
cd pera-counterexample
git checkout v1.0.0
export PATH="$HOME/.elan/bin:$PATH"
lake update
lake exe cache get Mathlib.Tactic Mathlib.Analysis.CStarAlgebra.Matrix Mathlib.LinearAlgebra.Matrix.Rank
python3 verify.py --output /tmp/pera-verification-fresh
```

Lean 4.24.0 and mathlib commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
are pinned. The verifier builds the project, audits all 18 named theorems,
rejects unfinished proofs and added axioms, and records source/log hashes.
Only Lean’s standard `propext`, `Classical.choice`, and `Quot.sound` occur.
The output directory must be new. First setup downloads compiler/library files;
no model weights, datasets or paid APIs are needed.

Optional numerical companion: install `examples/requirements.txt` under
Python 3.12.14, then run
`python examples/run_v2.py --output /tmp/pera-numerical-fresh.json`.
It uses exact rational matrix identities and float64 spectral norms.

## Scope

The result concerns the tied real parameterization and the specified theorem.
It does not refute empirical benchmark results, establish priority for this
observation, or introduce a new adapter. We found no prior public correction in
the sources recorded in the search note; that is not proof of first discovery.

These artifacts were separated from a broader research project. Their origin
is recorded in [PROVENANCE.json](PROVENANCE.json). The Lean proof sources are
unchanged; verification was rerun in this standalone repository. No author
messages have been sent.
