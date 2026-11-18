# PERA Theorem 1: claim scope and counterexample audit

Date: 2026-11-18

This note audits Appendix A.3 of [PERA v1](https://arxiv.org/html/2604.11841v1)
against the method definition in the same paper and the local counterexample
in this repository. It is a mathematical claim
audit, not a priority claim, a benchmark reproduction, or evidence that a new
adapter is useful.

## What the paper actually states

The method defines, over real matrices, an update of the form

$$
 M = BA + \sum_{i\leq j}h_{ij}
 (b_i\odot b_j)(a_i\odot a_j)^T.
$$

For nominal rank `r`, the expanded factor width is
`K = 2r + C(r,2) = r + r(r+1)/2`. Thus every actual PERA update has rank at
most `K`. The paper's Theorem 1 then claims

$$
 \min_{M\in S_{PERA}}\|M-E\|_2 \leq \sigma_{K+1}(E),
$$

where its proof says that `S_PERA` is contained in the rank-at-most-`K`
matrices and invokes Eckart--Young--Mirsky. That invocation has the inequality
backwards. If `S_PERA` is a subset of the rank-at-most-`K` set, minimizing over
`S_PERA` can only make the optimum larger, or equal. The containment justifies

$$
 \inf_{M\in S_{PERA}}\|M-E\|_2 \geq \sigma_{K+1}(E),
$$

not the claimed upper bound. The opposite useful upper bound follows from the
fact that `h=0` recovers LoRA:

$$
 \inf_{M\in S_{PERA}}\|M-E\|_2 \leq \sigma_{r+1}(E).
$$

So the general statement supported by the displayed definitions is the
one-sided sandwich

$$
 \sigma_{K+1}(E) \leq \inf_{M\in S_{PERA}}\|M-E\|_2
 \leq \sigma_{r+1}(E),
$$

with the usual convention for singular values beyond the matrix dimensions.

There is one important interpretive caveat. If `S_PERA` in the theorem were
silently intended to mean the larger class of *all* matrices expressible as a
sum of arbitrary rank-`r`, rank-`r`, and rank-`C(r,2)` terms, then an upper bound
by the rank-`K` optimum would describe that larger relaxation. It would still
not establish the bound for the tied polynomial parameterization actually
defined in equations (3)--(4). The paper does not state this relaxation, and
its proof explicitly calls the rank-bounded set a container for the PERA
hypothesis space.

## Counterexample scope

Take real `3 × 3` matrices, nominal `r=1`, and

$$
 n=(1,1,1)^T/\sqrt 3,\qquad P=I-nn^T.
$$

`P` is a rank-two orthogonal projector with singular values `(1,1,0)`. The
theorem's claimed right-hand side is therefore `sigma_3(P)=0`.

For `r=1`, every actual PERA update is

$$
 M=ba^T+h(b\odot b)(a\odot a)^T.
$$

The local proof gives `||P-M||_2 >= 1/sqrt(3)` for every real `a`, `b`, and
`h`:

* If `rank(M) <= 1`, Eckart--Young gives error at least `sigma_2(P)=1`.
* If `rank(M)=2`, the row space is `span(a, a⊙a)`. The vector
  `u=(a⊙a)/||a⊙a||` is defined and nonnegative. A unit vector `v` in the right
  kernel of `M` is orthogonal to `u`. Since `u` is nonnegative and has unit
  Euclidean norm, `n·u >= 1/sqrt(3)`. Decomposing `n` into its component along
  `u` and its orthogonal component gives `|n·v| <= sqrt(2/3)`. Therefore
  `||(P-M)v|| = ||Pv|| >= 1/sqrt(3)`.

This is a lower bound on the infimum, including parameter sequences that do not
attain a minimum. It does not depend on a numerical rank threshold, optimizer,
or sign of `h`. The theorem as written does not exclude `r=1`; its practical
description that `r` is small relative to the layer dimensions is not a
mathematical exclusion.

The argument is for real matrices, exactly the field used in the paper's
method definition. It does not claim a separate complex-valued theorem. It
also applies to the tied polynomial family; replacing the tied square/cross
terms with independent arbitrary low-rank factors would define a different,
larger model and could invalidate this particular counterexample.

## Verification status

The complete [Lean project](../README.md) now
checks the universal spectral-error bound, positive infimum, target rank and
projector properties, and a constructive strict comparison with rank-one LoRA.
The [receipt](../verification/result.json) records
18 audited theorem dependencies with only Lean's standard axioms. The exact
paper-to-statement correspondence remains a source interpretation checked in
this audit; Lean does not parse and adjudicate the paper's prose.

This corrects a theoretical claim. It does not show that PERA fails on
language-model tasks, invalidate the empirical tables, establish priority,
or supply a new practically superior adapter. Real task comparisons would
need matched parameter count, scaling, optimizer, memory and compute against
LoRA, LoHa/ABBA and HiRA.
