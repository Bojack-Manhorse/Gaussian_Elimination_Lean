import Gaussian.Matrix.DiagonalMatrices
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section ExistenceOfSolutions

lemma left_mul_matrix {m n : ℕ} (C : Matrix (Fin m) (Fin m) α) [Invertible C] (A B : Matrix (Fin m) (Fin n) α) (h : C * A = C * B) : A = B := by
  have h1 : ⅟C * (C * A) = ⅟C * (C * B) := by exact congrArg (HMul.hMul ⅟C) h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h1
  rw [invOf_mul_self] at h1
  simp at h1
  exact h1

lemma left_mul_matrix_iff {m n: ℕ} (C : Matrix (Fin m) (Fin m) α) [Invertible C] (A B : Matrix (Fin m) (Fin n) α) :
    C * A = C * B ↔ A = B := by
  apply Iff.intro
  . intro h
    exact left_mul_matrix C A B h
  . intro h
    exact congrArg (HMul.hMul C) h

/- After transforming a system by matrices `P` and `Q`, gives a way to go between solutions of the two systems. -/
lemma solutions_preserved_under_transvection (system : LinearSystem numVars numEqns α)
    (P : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P]
    (Q : Matrix (Fin numVars) (Fin numVars) α) [Invertible Q]
    (β : Matrix (Fin numVars) (Fin 1) α)
    : isSol system β ↔ isSol ⟨P * system.vars * Q, P * system.const⟩ (⅟Q * β) := by
  simp [isSol]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ ⅟Q, mul_invOf_self', Matrix.mul_one, Matrix.mul_assoc P _ _]
  apply Iff.symm
  apply left_mul_matrix_iff

end ExistenceOfSolutions

section NonDiagonalSolutions

/- Gives a solution to system via diagonalising `system.vars` to `new_system` and finding using `getSolDiagonal` on the `new_system`. -/
def get_solution_from_diagonalise (system : LinearSystem numVars numEqns α)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    : Matrix (Fin numVars) (Fin 1) α :=
  let new_system : LinearSystem numVars numEqns α := ⟨P_row * system.vars * P_col, P_row * system.const⟩
  P_col * getSolDiagonal new_system

/- Verifies the above solution is correct. -/
lemma check_solution (system : LinearSystem numVars numEqns α)
    (system_has_sol : hasSolution system)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    (h : isDiagonal (P_row * system.vars * P_col))
    : isSol system (get_solution_from_diagonalise system P_row P_col) := by
  rw [isSol]
  apply left_mul_matrix P_row
  rw [get_solution_from_diagonalise]
  rw [← Matrix.mul_assoc system.vars _ _]
  rw [← Matrix.mul_assoc P_row _ _]
  rw [← Matrix.mul_assoc P_row system.vars _]
  set ls₁ := P_row * system.vars * P_col with eq
  set ls₂ := P_row * system.const with eq₂
  set ls₃ : LinearSystem numVars numEqns α := ⟨ls₁, ls₂⟩ with eq₃
  rw [show ls₁ = ls₃.vars by rfl, show ls₂ = ls₃.const by rfl]
  rw [← isSol]
  apply check_diagonal_sol
  assumption
  obtain ⟨β, hb⟩ := system_has_sol
  rw [isSol] at hb
  have sol_to_ls₃: ls₃.vars * (⅟P_col * β) = ls₃.const := by
    rw [← show ls₁ = ls₃.vars by rfl, eq, ← show ls₂ = ls₃.const by rfl, eq₂ ]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ β, mul_invOf_self', Matrix.one_mul, Matrix.mul_assoc, hb]
  have exists_sol_to_ls₃ : hasSolution ls₃ := ⟨⅟P_col * β, sol_to_ls₃⟩
  aesop (add simp diagonal_system_has_no_solutions)

end NonDiagonalSolutions
