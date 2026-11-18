# Independent Lean audit of the PERA counterexample

Date: 2026-11-18

This audit originally inspected the Lean project in its source repository and ran the
compiler against the current files. The toolchain is pinned to Lean
`leanprover/lean4:v4.24.0`; the manifest pins mathlib at
`f897ebcf72cd16f89ab4577d0c826cd14afaafc7` and Batteries at
`8da40b72fece29b7d3fe3d768bac4c8910ce9bee`.

## What compiles

`PeraVerification.Counterexample` builds successfully with:

```text
lake build PeraVerification.Counterexample
✔ [3096/3096] Built PeraVerification.Counterexample
Build completed successfully
```

The core definition is exactly the real nominal-rank-one PERA family:

```text
pera a b h i j = b i * a j + h * (b i)^2 * (a j)^2
```

The theorem `pera_error_lower_bound` quantifies over every real `a`, `b`, and
`h` and proves

```text
1 / sqrt 3 ≤ ‖target - pera a b h‖
```

The norm is mathlib's Euclidean (`L2`) operator norm: the file explicitly opens
`Matrix.Norms.L2Operator` and uses `Matrix.l2_opNorm_mulVec`, not the Frobenius
or entrywise matrix norm. The proof constructs a nonzero vector annihilated by
both `a` and `a²`, proves the PERA matrix annihilates it, and applies the
operator-norm bound. The zero-`a` case has an explicit witness.

The same compiled file proves `optimal_error_lower_bound` for the set of all
errors and `optimal_error_positive`; it does not assume that an optimizer or
minimum exists. `target_not_representable` follows as a corollary.

An axioms print on the compiled declarations reports only Lean's ordinary
classical foundations:

```text
propext, Classical.choice, Quot.sound
```

There is no `sorry`, `admit`, `native_decide`, custom axiom, or `unsafe`
declaration in the formalization. The proof is therefore kernel-checked under
the pinned Lean/mathlib environment, subject to those standard library axioms.

## Target properties and the paper-theorem bridge

The repaired `PeraVerification.TargetProperties` module now also builds:

```text
lake build PeraVerification.TargetProperties
⚠ [3100/3100] Replayed PeraVerification.TargetProperties
Build completed successfully
```

It kernel-checks that the target is symmetric, idempotent, and has matrix rank
two. It also checks the explicit rational PERA witness used by the practical
comparison. `#print axioms` for `target_rank`, `target_mul_self`, and
`explicit_pera_witness` reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Together with the counterexample theorem, this formally establishes the bridge
to the paper's rank-based premise: the target has rank two, while every tied
real nominal-rank-one PERA update has strictly positive spectral error. The
paper's displayed Eckart--Young argument would assign the rank-two target a
zero `sigma_3` error, so the claimed upper-bound implication is false for the
stated family. The exact singular-value calculation is still expressed in the
report's elementary linear-algebra explanation; the Lean target module proves
rank/idempotence rather than introducing a separate singular-value API.

## Scope and limits

The formalization covers real 3-by-3 matrices and the tied square term for
nominal rank one. The final project verifier also checks a formal usefulness
comparison on this target: the PERA infimum lies in

```text
1 / sqrt 3 ≤ inf error ≤ sqrt (2 / 3) < 1,
```

every rank-one LoRA update has error at least `1`, and the explicit PERA witness
has error strictly below `1`. A separate formal factorization proves that
rank-two LoRA represents the target exactly. Thus this bounded algebraic task
does establish a real, useful expressivity difference on the constructed target;
it is not merely a theorem-bug artifact. It is still not a downstream task
usefulness result.

The formalization does not cover complex parameters, arbitrary nominal rank,
independent untied low-rank summands, LoHa/ABBA/HiRA comparisons, or transformer
training behavior. It does not verify the paper's empirical tables, the
paper-to-code correspondence, or the priority of this counterexample.

The theorem corrects a mathematical implication in the paper's Appendix A.3
argument; it does not show that PERA is useless. The final Lean modules
`Usefulness.lean` and `LoRAComparison.lean` now formally check the rational
construction, its operator-norm upper bound, the rank-one LoRA lower bound, and
the strict comparison. These remain a deliberately tiny matrix task, not a
language-model benchmark or evidence that PERA is novel overall.
