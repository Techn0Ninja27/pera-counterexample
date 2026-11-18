# A counterexample to PERA’s stated spectral approximation bound

**Draft for author review — 18 November 2026**

**Source:** *Polynomial Expansion Rank Adaptation: Enhancing Low-Rank Fine-Tuning with High-Order Interactions*, [Findings of ACL 2026, final PDF](https://aclanthology.org/2026.findings-acl.650.pdf), Appendix A.3, Theorem 1, printed page 13299 (PDF page 13). The same statement appears in [arXiv:2604.11841v1](https://arxiv.org/html/2604.11841v1).

## Summary

For the real, polynomially tied PERA parameterization, the rank upper bound does not imply that every matrix of that rank can be approximated arbitrarily closely. We give a rank-two target whose spectral approximation error is uniformly positive for nominal-rank-one PERA. The quantitative counterexample, target properties and infimum statement have been checked in Lean.

This finding concerns the stated theoretical guarantee. It does not assess the paper’s benchmark results or establish that PERA is ineffective.

## 1. The disputed implication

Write $K=2r+\binom r2$. Appendix A.3 places the PERA hypothesis family $S_{\mathrm{PERA}}$ inside the matrices of rank at most $K$, then concludes

$$
\inf_{M\in S_{\mathrm{PERA}}}\|M-E\|_2\le\sigma_{K+1}(E).
$$

The paper states this with `min`. We analyze the corresponding `inf` so no attainment assumption is needed. Our lower bound applies uniformly to every parameter value and hence to the infimum; if a minimum exists, the stated minimum claim is contradicted directly. Containment alone gives the opposite direction: restricting the feasible set cannot decrease the optimum. Since setting the polynomial coefficients to zero also recovers every rank-at-most-r LoRA update, the supported bounds are

$$
\boxed{\quad
\sigma_{K+1}(E)\le\inf_{M\in S_{\mathrm{PERA}}}\|M-E\|_2
\le\sigma_{r+1}(E).
\quad}
$$

These follow from the two set containments and Eckart–Young–Mirsky, with zero singular values beyond the matrix dimensions. We suggest this as a replacement bound, rather than a claim that either endpoint is attained by PERA. Our Lean project verifies the concrete counterexample below, not this general all-r statement through a separate singular-value API.

If the intended hypothesis family instead allows independently chosen low-rank square/cross summands, that is a different, larger family. A statement about that relaxation would need to be distinguished from the tied polynomial map defined in the method.

## 2. Counterexample

Set $r=1$, $m=n=3$, and

$$
P=I-\frac13\mathbf1\mathbf1^T
=\frac13\begin{pmatrix}2&-1&-1\\-1&2&-1\\-1&-1&2\end{pmatrix}.
$$

P is a symmetric rank-two orthogonal projector. Its singular values are $(1,1,0)$, so the disputed bound would give zero error. For this rank, the defined PERA family consists of

$$
M=ba^T+h(b\odot b)(a\odot a)^T,
\qquad a,b\in\mathbb R^3,\ h\in\mathbb R.
$$

**Proposition.** Every such M satisfies

$$
\boxed{\|P-M\|_2\ge\frac1{\sqrt3}.}
$$

### Proof

If M has rank at most one, Eckart–Young–Mirsky gives error at least $\sigma_2(P)=1$.

Otherwise M has rank two. Its row space equals the span of a and $a\odot a$, so it contains the nonnegative unit vector

$$
u=\frac{a\odot a}{\|a\odot a\|_2}.
$$

Choose a unit vector v in the right kernel of M. Then $u^Tv=0$. With $q=\mathbf1/\sqrt3$, nonnegativity gives $q^Tu=\|u\|_1/\sqrt3\ge1/\sqrt3$. Hence

$$
|q^Tv|\le\sqrt{1-(q^Tu)^2}\le\sqrt{2/3}.
$$

Therefore

$$
\|P-M\|_2\ge\|(P-M)v\|_2
=\|Pv\|_2=\sqrt{1-(q^Tv)^2}\ge1/\sqrt3.
$$

The lower bound is uniform. It excludes arbitrarily close approximation, including limits along unbounded parameter sequences, and therefore applies to the infimum. Negative h and degenerate factors are covered. ∎

## 3. Formal verification

The checked Lean proof uses an equivalent coordinate argument: construct a nonzero vector orthogonal to a and its entrywise square, prove the required three-coordinate inequality, and apply mathlib’s Euclidean operator norm. The zero-a case is handled separately.

Pinned environment:

- Lean **4.24.0**.
- mathlib commit **f897ebcf72cd16f89ab4577d0c826cd14afaafc7**.
- **18 audited theorems**, with successful build and explicit axiom audit.
- Only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms, unfinished proofs or native proof shortcuts.

The formalization includes the universal positive error bound, positive infimum, target rank/idempotence, and refutation of the assertion that every rank-two matrix can be approximated arbitrarily closely by this nominal-rank-one family. It does not parse the paper’s prose; correspondence with the method definition is a separate source audit.

Immutable artifacts:

- [Lean source and reproduction instructions](https://github.com/Techn0Ninja27/pera-counterexample/tree/v1.0.0).
- [Verification receipt](https://github.com/Techn0Ninja27/pera-counterexample/blob/v1.0.0/verification/result.json).
- [Axiom audit](https://github.com/Techn0Ninja27/pera-counterexample/blob/v1.0.0/verification/axioms.log).

## 4. A complementary positive result

The counterexample does not imply that PERA cannot improve on rank-one LoRA. Take

$$
a=(1,-1,0)^T,\quad b=(1/2,-1/2,0)^T,\quad h=2.
$$

Then $M=\operatorname{diag}(1,1,0)$. Lean proves

$$
\|P-M\|_2\le\sqrt{2/3}<1,
$$

and proves error at least 1 for **every** rank-one LoRA update on P. Thus the certified PERA optimum lies in

$$
[1/\sqrt3,\sqrt{2/3}].
$$

We do not claim its exact value. This witness uses seven trainable scalars versus six for rank-one LoRA. Rank-two LoRA uses twelve and represents P exactly. These are bounded algebraic comparisons with unequal parameter budgets, not downstream model-performance conclusions.

## 5. Requested clarification

We would appreciate confirmation of whether Appendix A.3 is intended to apply to the tied polynomial family as defined, or to an independent-summand relaxation. If it is the former, the counterexample rules out the stated upper bound; revising the statement and its expressivity interpretation appears appropriate. The method’s rank upper bound itself is unaffected.

We make no claim of priority for this observation and welcome corrections to our reading.
