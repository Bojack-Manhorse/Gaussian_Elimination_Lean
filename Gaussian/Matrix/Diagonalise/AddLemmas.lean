import Gaussian.Matrix.Diagonalise.PivotFunctions
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}


section AddLemmas

lemma diagonalOutsideInnerBlock_preserved_under_AddRowTransvection
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (coef : α)
    (i j : Fin numEqns)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock ((addRowTransvection coef i j) * M) index := by
  intro row col roworcol rowneqcol
  rw [addRowTransvection_lemma, Matrix.of_apply]
  by_cases roweqi : row = i
  . simp only [roweqi, ↓reduceIte]
    have colltind : col < index.1 := by omega
    have colneqi : i.1 ≠ col.1 := by omega
    have colneqj : j.1 ≠ col.1 := by omega
    have : M i col = 0 := Mdiag i col (by omega) (colneqi)
    have : M j col = 0 := Mdiag j col (by omega) (colneqj)
    aesop
  . aesop

lemma diagonalOutsideInnerBlock_preserved_under_AddColTransvection
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (coef : α)
    (i j : Fin numVars)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (addColTransvection coef i j)) index := by
  intro row col roworcol rowneqcol
  rw [addColTransvection_lemma, Matrix.of_apply]
  by_cases coleqj : col = j
  . simp only [coleqj, ↓reduceIte]
    have rowltind : row < index.1 := by omega
    have rowneqi : row.1 ≠ i.1 := by omega
    have rowneqj : row.1 ≠ j.1 := by omega
    have : M row j = 0 := Mdiag row j (by omega) (rowneqj)
    have : M row i = 0 := Mdiag row i (by omega) (rowneqi)
    aesop
  . aesop

/- Asserts that diagonalOutsideInnerBlock is preserved when applying `zeroOutColMatrix'`. -/
lemma diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock
      ((zeroOutColMatrix' M ⟨index.1,indlteqns⟩ index.2 ) * M) index := by
  intro row col roworcol rowneqcol
  rw [zeroOutColMatrix_lemma]
  simp [Matrix.of_apply]
  apply Or.elim roworcol
  . intro rowltind
    have rowneqind: row ≠ ⟨↑index, indlteqns⟩ := by aesop
    simp [rowneqind]
    have Mzero : M row col = 0 := by aesop
    aesop
  . intro colltind
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    split
    . assumption
    . have Mzero': M ⟨index.1, indlteqns⟩ col = 0 := by
        have indneqcol : index.1 ≠ col.1 := by omega
        specialize Mdiag (⟨index.1, by omega⟩) col (by aesop) (indneqcol)
        exact Mdiag
      rw [Mzero']
      field_simp
      assumption

/- Same as above but for `zeroOutRowMatrix`. -/
lemma diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (zeroOutRowMatrix' M index (by omega))) index := by
  intro row col roworcol rowneqcol
  rw [zeroOutRowMatrix_lemma]
  simp [Matrix.of_apply]
  apply Or.elim roworcol
  . intro rowltind
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    aesop
  . intro colltind
    have Mzero : M row col = 0 := Mdiag row col roworcol rowneqcol
    have colneqind: col ≠ index := by aesop
    simp [colneqind]
    have Mzero' : M ⟨index.1, by omega⟩ col = 0 := by
      have : index.1 ≠ col.1 := by omega
      specialize Mdiag ⟨index.1, by omega⟩ col (by aesop (add simp colltind)) (by assumption)
      exact Mdiag
    rw [Mzero, Mzero']
    field_simp

/- Proves that `M` and `(zeroOutColMatrix' M col_index) * M` have the same values on the `col_index` row. -/
lemma values_unchanged_by_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : ∀ col : Fin numVars, ((zeroOutColMatrix' M ⟨col_index.1, collteqn⟩ col_index.2) * M) ⟨col_index.1, collteqn⟩ col = M ⟨col_index.1, collteqn⟩ col := by
  intro col
  simp [zeroOutColMatrix_lemma]

/- Uses the previous theorem to show `zeroOutRowMatrix' _ col_index` is the same for `M` and `(zeroOutColMatrix' M col_index) * M`. -/
lemma same_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : zeroOutRowMatrix' M col_index collteqn = zeroOutRowMatrix' ((zeroOutColMatrix' M ⟨col_index.1, by omega⟩ (col_index.2)) * M) col_index collteqn := by
  have M_eq : M ⟨col_index.1, by omega⟩ col_index = ((zeroOutColMatrix' M ⟨col_index.1, by omega⟩ col_index.2) * M) ⟨col_index.1, by omega⟩ col_index := by
    aesop (add simp values_unchanged_by_zeroOutColMatrix)
  by_cases non_zero : M ⟨col_index.1, by omega⟩ col_index = 0
  . aesop (add simp zeroOutRowMatrix_lemma_when_zero)
  . have non_zero' : ((zeroOutColMatrix' M ⟨col_index.1, by omega⟩ col_index.2) * M) ⟨col_index.1, by omega⟩ col_index ≠ 0 := by aesop
    simp [zeroOutRowMatrix', non_zero_indicator, non_zero, add_assoc, non_zero']
    apply Fintype.sum_congr
    intro col
    aesop (add simp values_unchanged_by_zeroOutColMatrix)

lemma values_unchanged_by_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowlteqn : row_index < numVars)
    : ∀ row : Fin numEqns, (M * (zeroOutRowMatrix' M ⟨row_index.1, by omega⟩ row_index.2)) row ⟨row_index.1, rowlteqn⟩ = M row ⟨row_index.1, by omega⟩ := by
  intro row
  simp [zeroOutRowMatrix_lemma]

lemma same_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowlteqn : row_index < numVars)
    : zeroOutColMatrix' M row_index (by omega) = zeroOutColMatrix' (M * (zeroOutRowMatrix' M ⟨row_index.1, by omega⟩ (row_index.2))) row_index (by omega) := by
  have M_eq : M row_index ⟨row_index.1, by omega⟩ = (M * zeroOutRowMatrix' M ⟨↑row_index, by omega⟩ (row_index.2)) row_index ⟨↑row_index, by omega⟩ := by
    aesop (add simp values_unchanged_by_zeroOutRowMatrix)
  by_cases non_zero : M row_index ⟨row_index.1, by omega⟩ = 0
  . aesop (add simp zeroOutColMatrix_lemma_when_zero)
  . have non_zero': (M * zeroOutRowMatrix' M ⟨↑row_index, by omega⟩ (row_index.2)) row_index ⟨↑row_index, by omega⟩ ≠ 0 := by aesop
    simp [non_zero, non_zero', zeroOutColMatrix', non_zero_indicator, add_assoc]
    apply Fintype.sum_congr
    aesop (add simp values_unchanged_by_zeroOutRowMatrix)

lemma zero_row_and_col_after_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowlteqn : row_index < numVars)
    (non_zero : M row_index ⟨row_index.1, by omega⟩ ≠ 0)
    : ∀ row : Fin numEqns, ∀ col : Fin numVars, (row.1 = row_index ∨ col.1 = row_index) → row.1 ≠ col.1 →
      ((zeroOutColMatrix' M row_index (by omega)) * M * (zeroOutRowMatrix' M ⟨row_index.1, by omega⟩ (row_index.2))) row col = 0 := by
  intro row col row_or_col row_neq_col
  set zero_col := (zeroOutColMatrix' M row_index (by omega)) * M with eq
  have : ∀ r : Fin numEqns, r.1 ≠ row_index.1 → zero_col r ⟨row_index.1, by omega⟩ = 0 := by
    intro r r_neq
    have r_neq' : r ≠ row_index := by omega
    simp [eq, zeroOutColMatrix_lemma'', r_neq']
    field_simp
  rw [same_zeroOutRowMatrix, ← eq]
  have : ∀ r : Fin numEqns, zero_col r ⟨row_index.1, by omega⟩ = (zero_col * zeroOutRowMatrix' zero_col ⟨↑row_index, by omega⟩ (row_index.2)) r ⟨row_index.1, by omega⟩ := by
    intro row
    rw [values_unchanged_by_zeroOutRowMatrix zero_col]
  set zero_col_row := (zero_col * zeroOutRowMatrix' zero_col ⟨↑row_index, by omega⟩ (row_index.2)) with eq'
  have : zero_col row_index ⟨↑row_index, by omega⟩ = M row_index ⟨↑row_index, by omega⟩ := by
    simp [eq]
    rw [values_unchanged_by_zeroOutColMatrix M ⟨row_index.1, by omega⟩]
  have : zero_col row_index ⟨↑row_index, by omega⟩ ≠ 0 := by aesop
  have : ∀ c : Fin numVars, c.1 ≠ row_index.1 → zero_col_row row_index c = 0 := by
    intro c c_neq
    have c_neq' : c ≠ ⟨row_index.1, by omega⟩ := by aesop
    rw [eq']
    simp [zeroOutRowMatrix_lemma'', c_neq']
    field_simp
  apply Or.elim row_or_col
  . intro r
    have row_eq: row = row_index := by aesop
    rw [row_eq]
    have : col ≠ ⟨row_index.1, by omega⟩ := by aesop
    aesop
  . intro c
    have col_eq : col = ⟨row_index.1, by omega⟩ := by aesop
    aesop

end AddLemmas
