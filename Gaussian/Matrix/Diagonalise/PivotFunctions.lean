import Gaussian.Matrix.ExistenceOfSolutions
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section PivotFunctions

def non_zero_indicator (x : α) : α := if x = 0 then 0 else 1

def zeroOutColMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + (Matrix.stdBasisMatrix row_index row_index (non_zero_indicator (M row_index ⟨row_index.1, by omega⟩)))
    + -∑ (row : Fin numEqns), Matrix.stdBasisMatrix row row_index (M row ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)

lemma zeroOutColMatrix_lemma_when_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    (is_zero : M row_index ⟨row_index.1, by omega⟩ = 0)
    : zeroOutColMatrix' M row_index rowltvar = 1 := by
  simp [zeroOutColMatrix', non_zero_indicator, is_zero]

lemma zeroOutColMatrix_lemma'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) =
        Matrix.of (fun x y =>
          if x ≠ row_index ∧ y.1 = row_index.1 then
            - (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)
          else (1 : Matrix (Fin numEqns) (Fin numEqns) α) x y) := by
  rw [zeroOutColMatrix']
  apply Matrix.ext
  intro x y
  by_cases non_zero : M row_index ⟨row_index.1, by omega⟩ = 0
  . simp [non_zero, non_zero_indicator]
    aesop
    apply Matrix.one_apply_ne'
    have : y.1 ≠ x.1 := by omega
    aesop
  . by_cases y_row : y = row_index
    . by_cases x_row : x = row_index
      . simp [y_row, x_row, add_assoc, non_zero_indicator, non_zero]
        rw [Matrix.sum_apply row_index row_index Finset.univ _]
        subst y_row
        have almost_all_zero : ∀ c : Fin numEqns, c ≠ y → Matrix.stdBasisMatrix c y (M c ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) y y = 0 := by
          intro c c_neq_y
          aesop
        rw [Fintype.sum_eq_single y almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        field_simp
      . simp [y_row, x_row]
        rw [Matrix.sum_apply x row_index Finset.univ _]
        subst y_row
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop), zero_add, neg_inj]
        have almost_all_zero : ∀ row : Fin numEqns, row ≠ x → Matrix.stdBasisMatrix row y (M row ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) x y = 0 := by
          intro row row_neq_x
          aesop
        rw [Fintype.sum_eq_single x almost_all_zero, Matrix.StdBasisMatrix.apply_same]
    . have y_neq : y.1 ≠ row_index.1 := by omega
      aesop
      rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
      simp [Matrix.sum_apply, add_assoc]
      have : ∀ c : Fin numEqns, Matrix.stdBasisMatrix c row_index (M c ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩) x y = 0 := by
        intro c
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        aesop
      aesop

lemma zeroOutColMatrix_lemma''
    {n : ℕ}
    (A : Matrix (Fin numEqns) (Fin n) α)
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) * A =
        Matrix.of (fun x y =>
          if x ≠ row_index then A x y - ((A row_index y) * (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩))
          else A x y) := by
  rw [zeroOutColMatrix_lemma']
  apply Matrix.ext
  intro row col
  rw [Matrix.mul_apply]
  by_cases row_eq : row = row_index
  . simp [row_eq]
    rw [Fintype.sum_eq_single row_index]
    . simp
    . intro x x_neq
      rw [Matrix.one_apply_ne' x_neq]
      ring
  . simp [row_eq]
    rw [Fintype.sum_eq_add row row_index]
    . have row_neq_fin : row.1 ≠ row_index.1 := by omega
      simp [row_neq_fin]
      ring
    . exact row_eq
    . intro x
      rintro ⟨x_row, x_row_index⟩
      have x_row_index_fin : x.1 ≠ row_index.1 := by omega
      simp [x_row_index_fin]
      apply Or.inl
      apply Matrix.one_apply_ne'
      assumption

lemma zeroOutColMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) * M =
        Matrix.of (fun x y =>
          if x ≠ row_index then M x y - ((M row_index y) * (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩))
          else M x y) := by
  aesop (add simp zeroOutColMatrix_lemma'')

lemma zeroOutColMatrix_lemma_when_non_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    (non_zero : M row_index ⟨row_index.1, by omega⟩ ≠ 0)
    : ∀ row : Fin numEqns, row ≠ row_index → (((zeroOutColMatrix' M row_index rowltvar) * M) row ⟨row_index.1, by omega⟩ = 0) := by
  intro row rowneq
  simp [zeroOutColMatrix_lemma, rowneq]
  field_simp

def zeroOutRowMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (Matrix.stdBasisMatrix col_index col_index (non_zero_indicator (M ⟨col_index.1, by omega⟩ col_index)))
    + -∑ col : Fin numVars, Matrix.stdBasisMatrix col_index col (M ⟨col_index.1, by omega⟩ col / M ⟨col_index, by omega⟩ col_index)

lemma zeroOutRowMatrix_lemma_when_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (colltvar : col_index < numEqns)
    (is_zero : M ⟨col_index.1, by omega⟩ col_index = 0)
    : zeroOutRowMatrix' M col_index colltvar = 1 := by
  simp [zeroOutRowMatrix', non_zero_indicator, is_zero, constIndicator]

lemma zeroOutRowMatrix_lemma'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (zeroOutRowMatrix' M col_index collteqn) =
        Matrix.of (fun x y =>
          if y ≠ col_index ∧ x.1 = col_index.1 then
            - (M ⟨col_index.1, by omega⟩ y / M ⟨col_index, by omega⟩ col_index)
          else (1 : Matrix (Fin numVars) (Fin numVars) α) x y) := by
  rw [zeroOutRowMatrix']
  apply Matrix.ext
  intro x y
  by_cases non_zero : M ⟨col_index.1, by omega⟩ col_index = 0
  . simp [non_zero, non_zero_indicator, constIndicator]
    aesop
    apply Matrix.one_apply_ne'
    have : y.1 ≠ x.1 := by omega
    aesop
  . by_cases y_row : y = col_index
    . by_cases x_row : x = col_index
      . simp [y_row, x_row, add_assoc, non_zero_indicator, non_zero]
        rw [Matrix.sum_apply col_index col_index Finset.univ _]
        subst y_row
        have almost_all_zero : ∀ c : Fin numVars, c ≠ y → Matrix.stdBasisMatrix y c (M ⟨y.1, by omega⟩ c / M ⟨y.1, by omega⟩ y) y y = 0 := by
          aesop
        rw [Fintype.sum_eq_single y almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        field_simp
      . simp [constIndicator, non_zero, x_row, y_row]
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
        field_simp
        rw [Matrix.sum_apply]
        rw [Finset.sum_eq_zero]
        aesop (add simp Matrix.StdBasisMatrix.apply_of_ne)
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        aesop
    . simp [y_row, non_zero_indicator, non_zero]
      by_cases x_row : x = col_index
      . aesop (add simp Matrix.one_apply_ne')
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
        simp [Matrix.sum_apply]
        rw [Fintype.sum_eq_single y]
        aesop
        aesop
      . have x_col : x.1 ≠ col_index.1 := by omega
        simp [x_row, x_col, add_assoc, Matrix.sum_apply]
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        . simp
          apply Finset.sum_eq_zero
          intro x x_in
          rw [Matrix.StdBasisMatrix.apply_of_ne]
          aesop
        . aesop

lemma zeroOutRowMatrix_lemma''
    {n : ℕ}
    (A : Matrix (Fin n) (Fin numVars) α)
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (A * (zeroOutRowMatrix' M col_index collteqn)) =
        Matrix.of (fun x y =>
          if y ≠ col_index then A x y - ((A x col_index) * (M ⟨col_index.1, by omega⟩ y / M ⟨col_index.1, by omega⟩ col_index))
          else A x y
          ) := by
  rw [zeroOutRowMatrix_lemma']
  apply Matrix.ext
  intro row col
  rw [Matrix.mul_apply]
  by_cases col_eq : col = col_index
  . simp [col_eq]
    rw [Fintype.sum_eq_single col_index]
    . simp
    . intro x x_neq
      rw [Matrix.one_apply_ne x_neq]
      ring
  . simp [col_eq]
    rw [Fintype.sum_eq_add col col_index]
    . have col_neq_fin : col.1 ≠ col_index.1 := by omega
      simp [col_neq_fin]
      ring
    . assumption
    . intro x
      rintro ⟨x_row, x_col_index⟩
      have x_col_index_fin : x.1 ≠ col_index.1 := by omega
      simp [x_col_index_fin]
      aesop

lemma zeroOutRowMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (M * (zeroOutRowMatrix' M col_index collteqn)) =
        Matrix.of (fun x y =>
          if y ≠ col_index then M x y - ((M x col_index) * (M ⟨col_index.1, by omega⟩ y / M ⟨col_index.1, by omega⟩ col_index))
          else M x y) := by
  aesop (add simp zeroOutRowMatrix_lemma'')

lemma zeroOutRowMatrix_lemma_when_non_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    (non_zero : M ⟨col_index.1, by omega⟩ col_index ≠ 0)
    : ∀ col : Fin numVars, col ≠ col_index → ((M * (zeroOutRowMatrix' M col_index collteqn)) ⟨col_index.1, by omega⟩ col = 0) := by
  intro col colneq
  simp [zeroOutRowMatrix_lemma, colneq]
  field_simp

def zeroOutColMatrixInverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + -(Matrix.stdBasisMatrix row_index row_index (non_zero_indicator (M row_index ⟨row_index.1, by omega⟩)))
    + ∑ (row : Fin numEqns), Matrix.stdBasisMatrix row row_index (M row ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)

/- This lemma's proof is identical to `zeroOutColMatrix_lemma'`, is there a better way?-/
lemma zeroOutColMatrixInverse_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : (zeroOutColMatrixInverse M row_index rowltvar) =
        Matrix.of (fun x y =>
          if x ≠ row_index ∧ y.1 = row_index.1 then
            (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)
          else (1 : Matrix (Fin numEqns) (Fin numEqns) α) x y) := by
  rw [zeroOutColMatrixInverse]
  apply Matrix.ext
  intro x y
  by_cases non_zero : M row_index ⟨row_index.1, by omega⟩ = 0
  . simp [non_zero, non_zero_indicator]
    aesop
    apply Matrix.one_apply_ne'
    have : y.1 ≠ x.1 := by omega
    aesop
  . by_cases y_row : y = row_index
    . by_cases x_row : x = row_index
      . simp [y_row, x_row, add_assoc, non_zero_indicator, non_zero]
        rw [Matrix.sum_apply row_index row_index Finset.univ _]
        subst y_row
        have almost_all_zero : ∀ c : Fin numEqns, c ≠ y → Matrix.stdBasisMatrix c y (M c ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) y y = 0 := by
          intro c c_neq_y
          aesop
        rw [Fintype.sum_eq_single y almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        field_simp
      . simp [y_row, x_row]
        rw [Matrix.sum_apply x row_index Finset.univ _]
        subst y_row
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
        have almost_all_zero : ∀ row : Fin numEqns, row ≠ x → Matrix.stdBasisMatrix row y (M row ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) x y = 0 := by
          intro row row_neq_x
          aesop
        rw [Fintype.sum_eq_single x almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        ring
    . have y_neq : y.1 ≠ row_index.1 := by omega
      aesop
      rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
      simp [Matrix.sum_apply, add_assoc]
      have : ∀ c : Fin numEqns, Matrix.stdBasisMatrix c row_index (M c ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩) x y = 0 := by
        intro c
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        aesop
      aesop

lemma zeroOutColMatrixInverse_is_inverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) * (zeroOutColMatrixInverse M row_index rowltvar) = 1 := by
  rw [zeroOutColMatrix_lemma'']
  simp [zeroOutColMatrixInverse_lemma]
  apply Matrix.ext
  intro row col
  simp [Matrix.of_apply]
  aesop
  . have : row ≠ col := by omega
    have : row ≠ row_index := by omega
    simp [Matrix.one_apply_ne this, Matrix.one_apply, Eq.symm h]
    have : row_index = col := by omega
    aesop
  . apply Or.inl
    apply Matrix.one_apply_ne
    aesop

instance zeroOutColMatrix'_is_invertible
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Invertible (zeroOutColMatrix' M row_index rowltvar) := by
  apply Matrix.invertibleOfRightInverse _ (zeroOutColMatrixInverse M row_index rowltvar)
  apply zeroOutColMatrixInverse_is_inverse

def zeroOutRowMatrixInverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : Matrix (Fin numVars) (Fin numVars) α :=
  1 - (Matrix.stdBasisMatrix col_index col_index (non_zero_indicator (M ⟨col_index.1, by omega⟩ col_index)))
    + ∑ col : Fin numVars, Matrix.stdBasisMatrix col_index col (M ⟨col_index.1, by omega⟩ col / M ⟨col_index, by omega⟩ col_index)

lemma zeroOutRowMatrixInverse_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (zeroOutRowMatrixInverse M col_index collteqn) =
        Matrix.of (fun x y =>
          if y ≠ col_index ∧ x.1 = col_index.1 then
            (M ⟨col_index.1, by omega⟩ y / M ⟨col_index, by omega⟩ col_index)
          else (1 : Matrix (Fin numVars) (Fin numVars) α) x y) := by
  rw [zeroOutRowMatrixInverse]
  apply Matrix.ext
  intro x y
  by_cases non_zero : M ⟨col_index.1, by omega⟩ col_index = 0
  . simp [non_zero, non_zero_indicator, constIndicator]
    aesop
    apply Matrix.one_apply_ne'
    have : y.1 ≠ x.1 := by omega
    aesop
  . by_cases y_row : y = col_index
    . by_cases x_row : x = col_index
      . simp [y_row, x_row, add_assoc, non_zero_indicator, non_zero]
        rw [Matrix.sum_apply col_index col_index Finset.univ _]
        subst y_row
        have almost_all_zero : ∀ c : Fin numVars, c ≠ y → Matrix.stdBasisMatrix y c (M ⟨y.1, by omega⟩ c / M ⟨y.1, by omega⟩ y) y y = 0 := by
          aesop
        rw [Fintype.sum_eq_single y almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        field_simp
      . simp [constIndicator, non_zero, x_row, y_row]
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
        field_simp
        rw [Matrix.sum_apply]
        rw [Finset.sum_eq_zero]
        aesop (add simp Matrix.StdBasisMatrix.apply_of_ne)
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        aesop
    . simp [y_row, non_zero_indicator, non_zero]
      by_cases x_row : x = col_index
      . aesop (add simp Matrix.one_apply_ne')
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
        simp [Matrix.sum_apply]
        rw [Fintype.sum_eq_single y]
        aesop
        aesop
      . have x_col : x.1 ≠ col_index.1 := by omega
        simp [x_row, x_col, add_assoc, Matrix.sum_apply]
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        . simp
          apply Finset.sum_eq_zero
          intro x x_in
          rw [Matrix.StdBasisMatrix.apply_of_ne]
          aesop
        . aesop

lemma zeroOutRowMatrixInverse_is_inverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (zeroOutRowMatrixInverse M col_index collteqn) * (zeroOutRowMatrix' M col_index collteqn) = 1 := by
  simp [zeroOutRowMatrix_lemma'', zeroOutRowMatrixInverse_lemma]
  apply Matrix.ext
  intro row col
  simp [Matrix.of_apply]
  aesop
  . have : row = col_index := by omega
    aesop (add simp Matrix.one_apply)
  . apply Or.inl
    aesop (add simp Matrix.one_apply)

instance zeroOutRowMatrix'_is_invertible
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : Invertible (zeroOutRowMatrix' M col_index collteqn) := by
  apply Matrix.invertibleOfLeftInverse _ (zeroOutRowMatrixInverse M col_index collteqn)
  apply zeroOutRowMatrixInverse_is_inverse

/- Two lemmas to show that the identity is technically a row and column transvection. -/
lemma id_is_row_transvection
    (eqngtone : 1 < numEqns)
    : 1 = addRowTransvection (0 : α) ⟨0, by omega⟩ ⟨1, eqngtone⟩ := by
  simp [addRowTransvection]

lemma id_is_col_transvection
    (vargtone : 1 < numVars)
    : 1 = addColTransvection (0 : α) ⟨0, by omega⟩ ⟨1, vargtone⟩ := by
  simp [addColTransvection]

/- Given a matrix `M`, makes the entry at `M index index` non-zero by trying column then row swaps-/
def makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : (Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numVars) (Fin numVars) α) :=
  if h1 : index ≥ numEqns then (1, 1)
  else if h2 : M ⟨index.1, by omega⟩ index ≠ 0 then (1, 1)
  else
    let column := List.ofFn
      (fun x : Fin numEqns =>
        (M x index, x))
    let column_filtered := column.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
    if geq : column_filtered.length > 0
      then (swapRowMatrix (column_filtered[0]'(geq)).2 ⟨index.1, Nat.gt_of_not_le h1⟩, 1)
    else
      let index' : Fin numEqns := ⟨index.1, by omega⟩
      let row := List.ofFn (fun x : Fin numVars => (M index' x, x))
      let row_filtered := row.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
      if geq : row_filtered.length > 0
        then (1, swapColMatrix (row_filtered[0]'(geq)).2 index)
      else (1, 1)

lemma makeNonZeroAtDiag_self_inverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : let tuple := makeNonZeroAtDiag M index
      tuple.1 * tuple.1 * M * tuple.2 * tuple.2 = M := by
  simp [makeNonZeroAtDiag]
  aesop (add simp swapColMatrix_self_inverse) (add simp swapRowMatrix_self_inverse)
  set num := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0)) (List.ofFn fun x => (M ⟨index.1, by omega⟩ x, x)))[0].2
  rw [Matrix.mul_assoc M _ _]
  rw [swapColMatrix_self_inverse]
  aesop


lemma makeNonZeroAtDiag_fst_identity
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (col_zero : ∀ row : Fin numEqns, row.1 ≠ index.1 → M row index = 0 )
    : (makeNonZeroAtDiag M index).1 = 1 := by
  rw [makeNonZeroAtDiag]
  split
  . rfl
  . split
    . rfl
    . set ls := (List.filter (fun x => decide (index.1 < ↑x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
      have lszero : ls.length = 0 := by
        aesop
      simp [lszero]
      have : ¬ 0 < ls.length := by aesop
      aesop

lemma list_of_Fn_get_index {β : Type}{f : Fin numEqns → β} {a : β} (a_in_list : a ∈ List.ofFn f)
    : ∃ n : Fin numEqns, a = f n := by
  rw [List.mem_ofFn] at a_in_list
  simp_all only [Set.mem_range]
  obtain ⟨w, h⟩ := a_in_list
  subst h
  simp_all only [exists_apply_eq_apply']

lemma makeNonZeroAtDiag_snd_identity
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqn : index.1 < numEqns)
    (row_zero : ∀ col : Fin numVars, col.1 ≠ index.1 → M ⟨index.1, by omega⟩ col = 0)
  : (makeNonZeroAtDiag M index).2 = 1 := by
  rw [makeNonZeroAtDiag]
  split
  . rfl
  . split
    . rfl
    . set ls := (List.filter (fun x => decide (index.1 < ↑x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
      by_cases len : 0 < ls.length
      . simp [len]
      . simp [len]
        set ls_row := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0))
              (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x))) with eq
        have ls_row_zero: ¬ 0 < ls_row.length := by
          simp_all
          refine List.filter_eq_nil_iff.mpr ?_
          intro a
          intro a_in_list
          have : _ := list_of_Fn_get_index a_in_list
          obtain ⟨n, n_prop⟩ := this
          simp [n_prop]
          intro ngtind
          have : n.1 ≠ index.1 := by omega
          aesop
        simp [ls_row_zero]

/- Zeroes out the entire row and column at `index` except for `M index index`. -/
def pivotAtIndex
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  if h : numEqns ≤ index.1 then
    M
  else
    if Mzero : ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0
      then M
    else
      (zeroOutColMatrix' swapped ⟨index.1, by omega⟩ (index.2)) * swapped * (zeroOutRowMatrix' swapped index (by omega))

def pivotAtIndexTuple
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : ((Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numEqns) (Fin numEqns) α)) × ((Matrix (Fin numVars) (Fin numVars) α) × (Matrix (Fin numVars) (Fin numVars) α)) :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  let one_eqn := (1 : Matrix (Fin numEqns) (Fin numEqns) α)
  let one_var := (1 : Matrix (Fin numVars) (Fin numVars) α)
  if h : numEqns ≤ index.1 then
    ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
  else
    if Mzero : ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0
      then ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
    else
    ⟨⟨zeroOutColMatrix' swapped ⟨index.1, by omega⟩ (index.2),rowSwap ⟩, ⟨ colSwap, zeroOutRowMatrix' swapped index (by omega) ⟩⟩

lemma pivotAtIndex_eq_pivotAtIndexTuple
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : pivotAtIndex M index =
      (pivotAtIndexTuple M index).1.1 * (pivotAtIndexTuple M index).1.2 * M *(pivotAtIndexTuple M index).2.1 * (pivotAtIndexTuple M index).2.2 := by
  simp [pivotAtIndex, pivotAtIndexTuple]
  aesop (add simp Matrix.mul_assoc)

def pivotAtIndexInverseTuple
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : ((Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numEqns) (Fin numEqns) α)) × ((Matrix (Fin numVars) (Fin numVars) α) × (Matrix (Fin numVars) (Fin numVars) α)) :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  let one_eqn := (1 : Matrix (Fin numEqns) (Fin numEqns) α)
  let one_var := (1 : Matrix (Fin numVars) (Fin numVars) α)
  if h : numEqns ≤ index.1 then
    ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
  else
    if Mzero : ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0
      then ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
    else
    ⟨⟨zeroOutColMatrixInverse swapped ⟨index.1, by omega⟩ (index.2),rowSwap ⟩, ⟨ colSwap, zeroOutRowMatrixInverse swapped index (by omega) ⟩⟩

lemma pivotAtIndexInverseTuple_verify₁
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : let tuple := pivotAtIndexTuple M index
      let inverse_tuple := pivotAtIndexInverseTuple M index
      inverse_tuple.1.1 * tuple.1.1 = 1 := by
  simp [pivotAtIndexInverseTuple, pivotAtIndexTuple]
  set N₁ := (makeNonZeroAtDiag M index).1
  set N₂ := (makeNonZeroAtDiag M index).2
  aesop <;>
  apply Matrix.mul_eq_one_comm.mp <;>
  apply zeroOutColMatrixInverse_is_inverse

example (A B : Matrix (Fin 2) (Fin 2) α) : A * B = 1 → B * A = 1 := by apply?

lemma pivotAtIndexInverseTuple_verify₂
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : let tuple := pivotAtIndexTuple M index
      let inverse_tuple := pivotAtIndexInverseTuple M index
      tuple.2.2 * inverse_tuple.2.2 = 1 := by
  simp [pivotAtIndexInverseTuple, pivotAtIndexTuple]
  set N₁ := (makeNonZeroAtDiag M index).1
  set N₂ := (makeNonZeroAtDiag M index).2
  aesop <;>
  apply Matrix.mul_eq_one_comm.mp <;>
  apply zeroOutRowMatrixInverse_is_inverse

lemma pivotAtIndexInverseTuple_verify
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : let tuple := pivotAtIndexTuple M index
      let inverse_tuple := pivotAtIndexInverseTuple M index
      inverse_tuple.1.2 * inverse_tuple.1.1 * tuple.1.1 * tuple.1.2 * M * tuple.2.1 * tuple.2.2 * inverse_tuple.2.2 * inverse_tuple.2.1 = M := by
  simp [Matrix.mul_assoc, pivotAtIndexInverseTuple_verify₁, pivotAtIndexInverseTuple_verify₂]
  simp [pivotAtIndexInverseTuple, pivotAtIndexTuple]
  aesop <;>
  simp [← Matrix.mul_assoc, makeNonZeroAtDiag_self_inverse M index]

/- Asserts that a matrix `M : Matrix (Fin numEqns) (Fin numVars) α` is diagonal outside the submatrix of indices greater than or equal to `index`. -/
def diagonalOutsideInnerBlock (M : Matrix (Fin numEqns) (Fin numVars) α) (index : Fin numVars )
    : Prop :=
  ∀ row : Fin numEqns, ∀ col : Fin numVars, (row.1 < index.1 ∨ col.1 < index.1) → row.1 ≠ col.1 → M row col = 0

/- Alternate version which allows `index` to be equal to `numVars`. -/
def diagonalOutsideInnerBlock' (M : Matrix (Fin numEqns) (Fin numVars) α) (index : Fin (numVars + 1) )
    : Prop :=
  ∀ row : Fin numEqns, ∀ col : Fin numVars, (row.1 < index.1 ∨ col.1 < index.1) → row.1 ≠ col.1 → M row col = 0

lemma diagonalOutsideInnerBlock_same_as_isDiagonal
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : diagonalOutsideInnerBlock' M ⟨numVars, by omega⟩ ↔ isDiagonal M := by
  rw [diagonalOutsideInnerBlock', isDiagonal]
  aesop

lemma diagonalOutsideInnerBlock_holds_for_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : diagonalOutsideInnerBlock' M ⟨0, by omega⟩ := by
  intro row col row_or_col row_neq_col
  aesop



end PivotFunctions
