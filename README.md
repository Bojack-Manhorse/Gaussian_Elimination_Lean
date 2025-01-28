# Gaussian

We build on the Transvection file in Mathlib to formalise a computable version of Gaussian elimination in Lean 4.

## Set up

Given a system of linear equation with $m$ equations and $n$ variables over a field $F$, we'd like to give an algorithm to compute a potential solution to the system and verify that the solution given by the algorithm is indeed correct.

## Approach

We assume each of them $m$ equations are of the form $\sum\limits_{i = 1}^n a_{j, i} x_i - c_j = 0$ where $0 \leq j < m$ and $a_{j, i}, c_j$ are elements of the field $F$. 

We then interpret this as a system of two matices $M \in F^{m \times n}$ and $b \in F^{n \times 1}$, where $M_{j, i} = a_{j, i}$ and $b_{j} = c_j$. Our goal is to construct some $\overline{x} \in F^{n \times 1}$ such that $M \overline{x} = b$ and verify in Lean that $\overline{x}$ does indeed satisfy the equation.

We do this first by diagonalising the Matrix $M$, and keeping track of all the transvections used in the process. So suppose we can write $M$ as:

$$ M = P_{row} * D * P_{col} $$

where $P_{row} \in F^{m \times m}$ and $P_{col} \in F^{n \times n}$ are compositions of transvections, and $D$ is zero apart from elements on the leading diagonal.

We then find and verify a solution $\overline{y}$ to the system:

$$ D \overline{y} = P_{row} b $$

Then we deduce that $x \coloneqq P_{col}\overline{y}$ is a solution to the initial system.