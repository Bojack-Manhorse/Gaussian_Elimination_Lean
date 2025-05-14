import Gaussian.Matrix.Diagonalise.PivotFunctions
import Gaussian.Matrix.Diagonalise.ApplyingPivot

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section ApplyDiagonalise

def n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin (numVars + 1))
    : Matrix (Fin numEqns) (Fin numVars) α :=
  Fin.foldl (n.1) (fun Mat num => pivotAtIndex Mat ⟨num.1, by omega⟩) M

lemma fold_apply
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin (numVars))
    : Fin.foldl (n + 1) (fun Mat num => pivotAtIndex Mat ⟨num, by omega⟩) M = pivotAtIndex (Fin.foldl (n) (fun Mat num => pivotAtIndex Mat ⟨num, by omega⟩) M) ⟨n, by omega⟩ := by
  rw [Fin.foldl_succ_last]
  rfl

lemma fold_apply_corr
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin (numVars))
    : n_thDiagonaliseMatrix M ⟨n + 1, by omega⟩ = pivotAtIndex (n_thDiagonaliseMatrix M ⟨n, by omega⟩) ⟨n, by omega⟩ := by
  apply fold_apply

lemma n_th_diagonal_after_n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin (numVars + 1))
    (n_lt_eqns : n.1 ≤ numEqns)
    : diagonalOutsideInnerBlock' (n_thDiagonaliseMatrix M n) n := by
  rw [n_thDiagonaliseMatrix]
  rcases n with ⟨n, hn⟩
  induction' n with n ih
  . apply diagonalOutsideInnerBlock_holds_for_zero
  . simp at *
    specialize ih (by omega) (by omega)
    rw [fold_apply M ⟨n, by omega⟩]
    set mid := Fin.foldl (n) (fun Mat num => pivotAtIndex Mat ⟨num.1, by omega⟩) M
    apply diagonalOutsideInnerBlock_increased_by_pivot'
    . simpa
    . simp
      have : (⟨n, by omega⟩ : Fin (numVars + 1)) = ↑n := by
        refine Fin.eq_of_val_eq ?_
        simp
        apply Eq.comm.mp
        apply Nat.mod_eq_of_lt
        omega
      simp_rw [← this]
      assumption

def entireFold
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    :=
    n_thDiagonaliseMatrix M ⟨(min numVars numEqns), by omega⟩

lemma entireFold_is_diagonal
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : isDiagonal (entireFold M) := by
  set minn := (min numVars numEqns)
  rw [entireFold]
  set mid := n_thDiagonaliseMatrix M ⟨numVars ⊓ numEqns, by omega⟩
  apply (diagonalOutsideInnerBlock_same_as_isDiagonal' mid).mp
  apply n_th_diagonal_after_n_thDiagonaliseMatrix
  simp

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

def diagonalizeLeftUpToK
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (k : Fin (numVars + 1))
    : Array (Matrix (Fin numEqns) (Fin numEqns) α)
  := squashArrayOfTuples (Array.ofFn (fun n : Fin k => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.1))

lemma diagonalizeLeft_equal_diagonalizeLeftUpToK
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : diagonalizeLeft M = diagonalizeLeftUpToK M ⟨min numVars numEqns, by omega⟩ := by
  rw [diagonalizeLeft, diagonalizeLeftUpToK, squashArrayOfTuples]

def diagonalizeLeftMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  (diagonalizeLeft M).foldr (· * ·) 1

def diagonalizeRight
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Array (Matrix (Fin numVars) (Fin numVars) α) :=
  let minn := min numVars numEqns
  squashArrayOfTuples (Array.ofFn (fun n : Fin minn => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.2))

def diagonalizeRightUpToK
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (k : Fin (numVars + 1))
  : Array (Matrix (Fin numVars) (Fin numVars) α) :=
squashArrayOfTuples (Array.ofFn (fun n : Fin k => pivotAtIndexTuple (n_thDiagonaliseMatrix M ⟨n.1 - 1, by omega⟩) ⟨n.1, by omega⟩ |>.2))

lemma diagonalizeRightUpToK_decomp
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (k : Fin (numVars + 1))
    (h : k < numVars)
    : let tuple := pivotAtIndexTuple (n_thDiagonaliseMatrix M k) ⟨k.1, by omega⟩
    (diagonalizeRightUpToK M ⟨k.1 + 1, by omega⟩).foldr (· * ·) 1 = ((diagonalizeRightUpToK M ⟨k.1, by omega⟩).foldr (· * ·) 1 ) * tuple.2.1 * tuple.2.2 := by
  intro tuple
  aesop




lemma diagonalizeRight_equal_diagonalizeRightUpToK
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : diagonalizeRight M = diagonalizeRightUpToK M ⟨min numVars numEqns, by omega⟩ := by
  rw [diagonalizeRight, diagonalizeRightUpToK, squashArrayOfTuples]

def diagonalizeRightMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (Matrix (Fin numVars) (Fin numVars) α) :=
  (diagonalizeRight M).foldl (· * ·) 1

lemma check_diagonalize_aux
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (k : Fin (numVars + 1))
    : n_thDiagonaliseMatrix M k = ((diagonalizeLeftUpToK M k).foldr (· * ·) 1) * M * ((diagonalizeRightUpToK M k).foldr (· * ·) 1) := by
  rcases k with ⟨k, k_leq⟩
  induction' k with k ih
  . rw [n_thDiagonaliseMatrix]
    simp
    have left_mat : Array.foldr (fun x1 x2 => x1 * x2) 1 (diagonalizeLeftUpToK M 0) = 1 := rfl
    have right_mat : Array.foldr (fun x1 x2 => x1 * x2) 1 (diagonalizeRightUpToK M 0) = 1 := rfl
    rw [left_mat, right_mat]
    simp
  . specialize ih k_leq


lemma check_diagonalize
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    --(var_pos : numVars > 0)
    : entireFold M =  (diagonalizeLeftMatrix M) * M * (diagonalizeRightMatrix M) := by
  rw [diagonalizeLeftMatrix, diagonalizeRightMatrix, entireFold, n_thDiagonaliseMatrix, diagonalizeRight_equal_diagonalizeRightUpToK, diagonalizeLeft_equal_diagonalizeLeftUpToK]
  --induction' (numVars ⊓ numEqns) with n ih




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
