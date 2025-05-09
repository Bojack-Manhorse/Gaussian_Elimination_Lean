import Gaussian.Matrix.Diagonalise.ApplyingPivot

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section ApplyDiagonalise

def n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin numVars)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  Fin.foldl n.1 (fun Mat num => pivotAtIndex Mat ⟨num.1, by omega⟩) M

lemma fold_apply
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin numVars)
    : Fin.foldl (n + 1) (fun Mat num => pivotAtIndex Mat ⟨num, by omega⟩) M  = pivotAtIndex (Fin.foldl (n) (fun Mat num => pivotAtIndex Mat ⟨num, by omega⟩) M) ⟨n, by omega⟩ := by
  rw [Fin.foldl_succ_last]
  rfl

lemma n_th_diagonal_after_n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin numVars)
    (n_lt_eqns : n.1 < numEqns)
    : diagonalOutsideInnerBlock (n_thDiagonaliseMatrix M n) n := by
  rw [n_thDiagonaliseMatrix]
  rcases n with ⟨n, hn⟩
  induction' n with n ih
  . aesop (add simp diagonalOutsideInnerBlock)
  . rw [fold_apply M ⟨n, by omega⟩]
    specialize ih (by omega) (Nat.lt_of_succ_lt n_lt_eqns)
    apply diagonalOutsideInnerBlock_increased_by_pivot
    . exact n_lt_eqns
    . aesop
    . exact ih

def secondLastFold
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    :=
    n_thDiagonaliseMatrix M ⟨(min numVars numEqns) - 1, by omega⟩

lemma n_th_diagonal_secondLastFold
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    (eqn_pos : numEqns > 0)
    : diagonalOutsideInnerBlock (secondLastFold M var_pos) ⟨(min numVars numEqns)- 1, by omega⟩ := by
    apply n_th_diagonal_after_n_thDiagonaliseMatrix
    aesop
    omega


def diagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  pivotAtIndex (secondLastFold M var_pos) ⟨(min numVars numEqns )- 1, by omega⟩

lemma diagonal_after_pivot_secondLastFold
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    (eqn_pos : numEqns > 0)
    : let minn := min numVars numEqns
      isDiagonal (pivotAtIndex (secondLastFold M var_pos) ⟨minn - 1, by omega⟩) := by
  set minn := min numVars numEqns
  set pivoted := pivotAtIndex (secondLastFold M var_pos) ⟨minn - 1, by omega⟩
  have : diagonalOutsideInnerBlock (secondLastFold M var_pos) ⟨minn - 1, by omega⟩ := n_th_diagonal_secondLastFold M var_pos eqn_pos
  have diag_out : diagonalOutsideInnerBlock (pivoted) ⟨minn - 1, by omega⟩ := by
    apply diagonalOutsideInnerBlock_preserved_by_pivot
    . simp_all only [gt_iff_lt, minn]; omega
    . assumption
  intro minnt row col row_neq_col
  have eq : minn = minnt := rfl
  by_cases outside : row < minn - 1 ∨ col < minn - 1
  . apply Or.elim outside <;> intro row_lt_minn <;> specialize diag_out row col (by aesop) row_neq_col <;> exact diag_out
  . push_neg at outside
    simp [pivotAtIndex]
    have eqn_gt_min : ¬ numEqns ≤ minn - 1 := by omega
    simp [eqn_gt_min]
    by_cases all_zero : ∀ (row : Fin numEqns) (col : Fin numVars), minnt ≤ ↑row + 1 → minnt ≤ ↑col + 1 → ↑row = minnt - 1 ∨ ↑col = minnt - 1 → secondLastFold M var_pos row col = 0
    . simp_all only [gt_iff_lt, ne_eq, tsub_le_iff_right, inf_le_iff, implies_true, ↓reduceIte, minn, pivoted, minnt]
      simp_all only [not_le, minn]
      obtain ⟨left, right⟩ := outside
      specialize all_zero row col (by aesop) (by aesop) (by omega)
      exact all_zero
    . simp_all only [gt_iff_lt, ne_eq, tsub_le_iff_right, inf_le_iff, implies_true, ↓reduceIte, minn, pivoted, minnt]
      obtain ⟨left, right⟩ := outside
      set swapped := (makeNonZeroAtDiag (secondLastFold M var_pos) ⟨numVars ⊓ numEqns - 1, by omega⟩).1 * secondLastFold M var_pos * (makeNonZeroAtDiag (secondLastFold M var_pos) ⟨numVars ⊓ numEqns - 1, by omega⟩).2
      have : swapped ⟨minn - 1, by omega⟩ ⟨minn - 1, by omega⟩ ≠ 0 := by
        apply zero_after_makeNonZeroAtDiag
        . aesop
        . aesop
      set zero_col := zeroOutColMatrix' swapped ⟨numVars ⊓ numEqns - 1, by omega⟩ (by simp; omega) * swapped with zero_col_eq
      apply zero_row_and_col_after_pivot
      . assumption
      . simp; omega
      . simp; omega
      . simp; omega

lemma diagonalize_is_diagonal
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    (eqn_pos : numEqns > 0)
    : isDiagonal (diagonaliseMatrix M var_pos) := by
  rw [diagonaliseMatrix]
  apply diagonal_after_pivot_secondLastFold
  assumption

def squashArrayOfTuples
    {β : Type}
    (as : Array (β × β))
    : Array β :=
  as.foldl (fun x y => (x.push y.1).push y.2) (#[])

def diagonalizeLeftUptok
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (k : Fin ((min numVars numEqns) + 1))
    : Array (Matrix (Fin numEqns) (Fin numEqns) α) :=
  squashArrayOfTuples (Array.ofFn (fun n : Fin k => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.1))

--diagonalizeLeftUptok * M * diagonalizeRightUptok = n_thDiagonaliseMatrix

/- A vector contaning all the elements to the left of M in `diagonaliseMatrix M`, specifically all the row operations. -/
def diagonalizeLeft
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    --(var_pos : numVars > 1)
    --(eqn_pos : numEqns > 1)
    : Array (Matrix (Fin numEqns) (Fin numEqns) α) :=
  let minn := min numVars numEqns
  squashArrayOfTuples (Array.ofFn (fun n : Fin minn => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.1))

def diagonalizeLeftMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    --(var_pos : numVars > 1)
    --(eqn_pos : numEqns > 1)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  (diagonalizeLeft M).foldr (· * ·) 1

def diagonalizeRight
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Array (Matrix (Fin numVars) (Fin numVars) α) :=
  let minn := min numVars numEqns
  squashArrayOfTuples (Array.ofFn (fun n : Fin minn => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.2))

def diagonalizeRightMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (Matrix (Fin numVars) (Fin numVars) α) :=
  (diagonalizeRight M).foldl (· * ·) 1

lemma check_diagonalize
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    : diagonaliseMatrix M var_pos =  (diagonalizeLeftMatrix M) * M * (diagonalizeRightMatrix M) := by
  rw [diagonalizeLeftMatrix, diagonalizeRightMatrix, diagonaliseMatrix]
  sorry

lemma diagonalizeLeft_invertible
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Matrix.det ((Array.foldr (· * ·) (1 : Matrix (Fin numEqns) (Fin numEqns) α) (diagonalizeLeft M))) ≠ 0 := by sorry

/- A vector containing all the elements to the right of M in `diagonaliseMatrix M`, so all the column operations. -/




lemma verify_diagonalize_left_right
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (vars_pos : numVars > 0)
    : diagonaliseMatrix M vars_pos = (Array.foldr (· * ·) (1 : Matrix (Fin numEqns) (Fin numEqns) α) (diagonalizeLeft M)) * M * (Array.foldl (· * ·) (1 : Matrix (Fin numVars) (Fin numVars) α) (diagonalizeRight M)) := sorry

def get_solution_of_system
    (system : LinearSystem numEqns numVars α)
    : Matrix (Fin numVars) (Fin 1) α :=
  get_solution_from_diagonalise system

end ApplyDiagonalise
