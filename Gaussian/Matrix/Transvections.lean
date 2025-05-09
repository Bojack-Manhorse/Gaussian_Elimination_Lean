import Gaussian.Matrix.SystemsOfLinearEquations
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α]

variable {numVars numEqns : ℕ}

section Transvections

/- Set `(c : α)` implicit? -/
/- Put c not zero as assumption in subseuent lemmas rather than in lemma-/
/- Try not to require proofs in the assumptions of definitions-/
/- From Mathlib Transvection 78-/
def addRowTransvection (c : α) (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α  :=
  1 + Matrix.stdBasisMatrix i j c

/- From Mathlib Transvection 78-/
def addColTransvection (c : α) (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + Matrix.stdBasisMatrix i j c

/- Do row₁ row₂ maybe?-/
/- A `numEqns × numEqns` matrix `P` such that for any matrix `A`, `P * A` represents swapping rows `i, j` of `A`. -/
def swapRowMatrix (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + ( -Matrix.stdBasisMatrix i i 1 + -Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A `numVars × numVars` `P` such that for any matrix `A`, `A * P` represents swapping columns `i, j` of `A`. -/
def swapColMatrix' (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (- Matrix.stdBasisMatrix i i 1 + - Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

def swapColMatrix (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (- Matrix.stdBasisMatrix i i 1 + - Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A type saying that a matrix is of the form in `addRowTransvection`. -/
abbrev addRowType :=
  {x : Matrix (Fin numEqns) (Fin numEqns) α // ∃ coef : α, ∃ i j : Fin numEqns, i ≠ j ∧ x = addRowTransvection coef i j}

/- A type saying that a matrix is of the form in `addColTransvection`. -/
abbrev addColType :=
  {x : Matrix (Fin numVars) (Fin numVars) α // ∃ coef : α, ∃ i j : Fin numVars, i ≠ j ∧ x = addColTransvection coef i j}

end Transvections

section TransvectionLemmas

/- Lemma that describes `addRowTransvection` in terms of `Matrix.of`. -/
lemma addRowTransvection_lemma (c : α) (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (addRowTransvection c i j) * M =
      Matrix.of (fun x y =>
        if x = i then M i y + c * M j y
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp [addRowTransvection, Matrix.add_mul]
  aesop (add simp Matrix.StdBasisMatrix.mul_left_apply_same)

/- Lemma that describes `addColTransvection` in terms of `Matrix.of`. -/
lemma addColTransvection_lemma (c : α) (i j : Fin numVars) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : M * (addColTransvection c i j) =
      Matrix.of (fun x y =>
        if y = j then M x j + c * M x i
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp only [addColTransvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.of_apply]
  aesop (add simp mul_comm) (add simp Matrix.StdBasisMatrix.mul_right_apply_same)

/- Lemma that describes `swapRowMatrix` in terms of `Matrix.of`. -/
lemma swapRowMatrix_lemma (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (swapRowMatrix i j) * M =
      Matrix.of (fun x y =>
        if x = i then M j y
        else if x = j then M i y
        else M x y) := by
  apply Matrix.ext
  intro row col
  simp only [swapRowMatrix, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.add_apply, Matrix.neg_apply]
  apply Or.elim (eq_or_ne row i)
  . intro roweqi
    simp only [roweqi, ↓reduceIte]
    apply Or.elim (eq_or_ne i j)
    . intro ieqj
      simp only [ieqj, Matrix.StdBasisMatrix.mul_left_apply_same, one_mul,
        add_neg_cancel_comm_assoc, neg_add_cancel_left, Matrix.of_apply, ↓reduceIte]
    . intro ineqj
      simp only [Matrix.StdBasisMatrix.mul_left_apply_same, one_mul, ne_eq, ineqj,
        not_false_eq_true, Matrix.StdBasisMatrix.mul_left_apply_of_ne, neg_zero, add_zero,
        add_neg_cancel, zero_add, Matrix.of_apply, ↓reduceIte]
  . aesop

lemma swapRowMatrix_self_inverse
    (i j : Fin numEqns)
    : (swapRowMatrix i j) * (swapRowMatrix i j) = (1 : Matrix (Fin numEqns) (Fin numEqns) α) := by
  apply Matrix.ext
  intro row col
  simp [swapRowMatrix_lemma]
  rw [swapRowMatrix]
  aesop (add simp Matrix.stdBasisMatrix) (add simp Matrix.one_apply)

instance swapRowMatrix_is_invertible
    (i j : Fin numEqns)
    : Invertible (swapRowMatrix i j : Matrix (Fin numEqns) (Fin numEqns) α) := by
  apply Matrix.invertibleOfRightInverse (swapRowMatrix i j) (swapRowMatrix i j)
  aesop (add simp swapRowMatrix_self_inverse)

/- Lemma that describes `swapColMatrix` in terms of `Matrix.of`. -/
lemma swapColMatrix_lemma
    {n : ℕ}
    (i j : Fin numVars)
    (M : Matrix (Fin n) (Fin numVars) α)
    : M * (swapColMatrix i j) =
      Matrix.of (fun x y =>
        if y = i then M x j
        else if y = j then M x i
        else M x y ) := by
  apply Matrix.ext
  intro row col
  simp only [swapColMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply]
  apply Or.elim (eq_or_ne col i)
  . intro coleqi
    simp only [coleqi, Matrix.StdBasisMatrix.mul_right_apply_same, mul_one, add_neg_cancel_left,
      ↓reduceIte]
    apply Or.elim (eq_or_ne i j)
    . intro ieqj
      simp only [ieqj, Matrix.StdBasisMatrix.mul_right_apply_same, mul_one, neg_add_cancel_left]
    . intro ineqj
      simp [ineqj]
  . aesop

lemma swapColMatrix_self_inverse
    (i j : Fin numVars)
    : (swapColMatrix i j) * (swapColMatrix i j) = (1 : Matrix (Fin numVars) (Fin numVars) α) := by
  apply Matrix.ext
  intro row col
  simp [swapColMatrix_lemma]
  rw [swapColMatrix]
  aesop (add simp Matrix.stdBasisMatrix) (add simp Matrix.one_apply)

instance swapColMatrix_is_invertible
    (i j : Fin numVars)
    : Invertible (swapColMatrix i j : Matrix (Fin numVars) (Fin numVars) α) := by
  apply Matrix.invertibleOfRightInverse (swapColMatrix i j) (swapColMatrix i j)
  aesop (add simp swapColMatrix_self_inverse)

end TransvectionLemmas
