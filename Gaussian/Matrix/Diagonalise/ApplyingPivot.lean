import Gaussian.Matrix.Diagonalise.PivotFunctions
import Gaussian.Matrix.Diagonalise.SwapLemmas
import Gaussian.Matrix.Diagonalise.AddLemmas
import Gaussian.Matrix.DiagonalMatrices

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section ApplyingPivot

lemma diagonalOutsideInnerBlock_preserved_by_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (inlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (pivotAtIndex M index) index := by
  rw [pivotAtIndex]
  have neindge : ¬ index.1 ≥ numEqns := by omega
  simp [neindge]
  split
  . assumption
  set swapped := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2
  have swapped_diag : diagonalOutsideInnerBlock swapped index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag)
  have zero_swapped_diag : diagonalOutsideInnerBlock ((zeroOutColMatrix' swapped ⟨index.1, inlteqns⟩ (index.2)) * swapped) index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix)
  rw [same_zeroOutRowMatrix]
  apply diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix
  . assumption
  . apply diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix
    assumption

lemma diagonalOutsideInnerBlock_preserved_by_pivot'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (inlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock' M index)
    : diagonalOutsideInnerBlock' (pivotAtIndex M index) index := by
  rw [pivotAtIndex]
  have neindge : ¬ index.1 ≥ numEqns := by omega
  simp [neindge]
  split
  . aesop
  set swapped := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2 with swap_rw
  have swapped_diag : diagonalOutsideInnerBlock' swapped index := by
    apply diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag'
    aesop
  have zero_swapped_diag : diagonalOutsideInnerBlock' ((zeroOutColMatrix' swapped ⟨index.1, inlteqns⟩ (index.2)) * swapped) index := by
    apply diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix'
    aesop
  rw [same_zeroOutRowMatrix]
  set zeroo := (zeroOutColMatrix' swapped ⟨index.1, inlteqns⟩ (by aesop) * swapped)
  have : _ := diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix' zeroo index (inlteqns) zero_swapped_diag
  aesop

lemma diagonalOutsideInnerBlock_increased_by_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1.succ < numEqns)
    (indltvars : index.1.succ < numVars)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : (diagonalOutsideInnerBlock (pivotAtIndex M index) ⟨index.1 + 1, by omega⟩) := by
  have pivotMdiag : diagonalOutsideInnerBlock (pivotAtIndex M index) index :=
    diagonalOutsideInnerBlock_preserved_by_pivot M index (by omega) Mdiag
  intro row col roworcol roweqcol
  simp_all only [Nat.succ_eq_add_one, ne_eq]
  simp [pivotAtIndex]
  have eqngtind: ¬ numEqns ≤ index.1 := by omega
  simp [eqngtind]
  split
  . aesop
    . have rowor: row.1 = index.1 ∨ row.1 < index.1 := by omega
      apply Or.elim rowor
      . intro roweqind
        aesop
        by_cases col_or : index ≤ col
        . specialize h row col (by omega) (col_or) (by aesop)
          exact h
        . aesop
      . aesop
    . have color: col.1 = index.1 ∨ col.1 < index.1 := by omega
      apply Or.elim color
      . intro coleqind
        by_cases row_or : index.1 ≤ row
        . specialize h row col (row_or) (by omega) (by aesop)
          exact h
        . aesop
      . aesop
  . set N := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2 with eq_N
    have : N ⟨index.1, by omega⟩ index ≠ 0 := by aesop (add simp zero_after_makeNonZeroAtDiag)
    rw [Matrix.mul_assoc]
    set zeroed_row := (N * zeroOutRowMatrix' N index (by omega)) with eq
    have : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = 0 := by
      intro col' col_neq
      rw [eq]
      aesop (add simp zeroOutRowMatrix_lemma_when_non_zero)
    have : zeroed_row ⟨index.1, by omega⟩ index ≠ 0 := by
      rw [eq, zeroOutRowMatrix_lemma, Matrix.of_apply]
      simp
      assumption
    set zeroed_row_col := (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (index.2)) * zeroed_row with eq'
    have row_is_eq : ∀ row' : Fin numEqns, row'.1 ≠ index.1 → zeroed_row_col row' index = 0 := by
      intro row' row_neq
      rw [eq']
      have row_neq_fin: row' ≠ ⟨index.1, by omega⟩ := by aesop
      simp [zeroOutColMatrix_lemma, Matrix.of_apply, row_neq_fin]
      field_simp
    have col_is_eq : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = zeroed_row_col ⟨index.1, by omega⟩ col' := by
      intro col' col_neq
      rw [eq', zeroOutColMatrix_lemma, Matrix.of_apply]
      simp
    apply Or.elim roworcol
    . intro rowltind1
      have rowltind: row.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le rowltind)
      . intro roweqind
        have colneqind: col ≠ index := by
          apply Fin.ne_of_val_ne
          rw [← roweqind]
          exact fun a => roweqcol (id (Eq.symm a))
        specialize col_is_eq col colneqind
        rw [eq'] at col_is_eq
        have row_eq_ind_fin : row = ⟨index.1, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr roweqind
        rw [row_eq_ind_fin]
        have simp_N: (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (by omega)) = zeroOutColMatrix' N ⟨index.1, by omega⟩ (by omega) := by
          rw [eq]
          rw [same_zeroOutColMatrix N]
          omega
        rw [← simp_N]
        simp [zeroOutColMatrix_lemma]
        rw [eq]
        simp [zeroOutRowMatrix_lemma, colneqind]
        field_simp
      . intro rowltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        apply pivotMdiag
        . exact Or.inl rowltind
        . exact fun h => (by simp_all [N, zeroed_row])
    . intro colltind1
      have colleind : col.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le colleind)
      . intro coleqind
        rw [eq]
        rw [← Matrix.mul_assoc]
        have h : index.1 < numEqns := Nat.gt_of_not_le eqngtind
        set zeroed_col := (zeroOutColMatrix' N ⟨index.1, h⟩ (index.2)) * N with eq'''
        have col_eq_ind_fin : col = index := Fin.eq_of_val_eq coleqind
        have simp_N : zeroOutRowMatrix' zeroed_col index (h) = zeroOutRowMatrix' N index (h) := by
          rw [eq''']
          rw [same_zeroOutRowMatrix N]
        rw [← simp_N]
        simp [zeroOutRowMatrix_lemma, col_eq_ind_fin]
        rw [eq''']
        have row_neq_index : row ≠ ⟨index.1, by omega⟩ := by
          apply Fin.ne_of_val_ne
          rw [← coleqind]
          assumption
        simp [zeroOutColMatrix_lemma, row_neq_index]
        field_simp
      . intro colltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        specialize pivotMdiag row col (by aesop) (by aesop)
        exact pivotMdiag

lemma diagonalOutsideInnerBlock_increased_by_pivot'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin (numVars))
    (indlteqns : index.1.succ < numEqns)
    (Mdiag : diagonalOutsideInnerBlock' M index)
    : (diagonalOutsideInnerBlock' (pivotAtIndex M index) ⟨index.1 + 1, by omega⟩) := by
  have pivotMdiag : diagonalOutsideInnerBlock' (pivotAtIndex M index) index :=
    diagonalOutsideInnerBlock_preserved_by_pivot' M index (by omega) Mdiag
  intro row col roworcol roweqcol
  simp_all only [Nat.succ_eq_add_one, ne_eq]
  simp [pivotAtIndex]
  have eqngtind: ¬ numEqns ≤ index.1 := by omega
  simp [eqngtind]
  split
  . aesop
    . have rowor: row.1 = index.1 ∨ row.1 < index.1 := by omega
      apply Or.elim rowor
      . intro roweqind
        aesop
        by_cases col_or : index ≤ col
        . specialize h row col (by omega) (col_or) (by aesop)
          exact h
        . aesop
      . aesop
    . have color: col.1 = index.1 ∨ col.1 < index.1 := by omega
      apply Or.elim color
      . intro coleqind
        by_cases row_or : index.1 ≤ row
        . specialize h row col (row_or) (by omega) (by aesop)
          exact h
        . aesop
      . aesop
  . set N := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2 with eq_N
    have : N ⟨index.1, by omega⟩ index ≠ 0 := by aesop (add simp zero_after_makeNonZeroAtDiag)
    rw [Matrix.mul_assoc]
    set zeroed_row := (N * zeroOutRowMatrix' N index (by omega)) with eq
    have : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = 0 := by
      intro col' col_neq
      rw [eq]
      aesop (add simp zeroOutRowMatrix_lemma_when_non_zero)
    have : zeroed_row ⟨index.1, by omega⟩ index ≠ 0 := by
      rw [eq, zeroOutRowMatrix_lemma, Matrix.of_apply]
      simp
      assumption
    set zeroed_row_col := (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (index.2)) * zeroed_row with eq'
    have row_is_eq : ∀ row' : Fin numEqns, row'.1 ≠ index.1 → zeroed_row_col row' index = 0 := by
      intro row' row_neq
      rw [eq']
      have row_neq_fin: row' ≠ ⟨index.1, by omega⟩ := by aesop
      simp [zeroOutColMatrix_lemma, Matrix.of_apply, row_neq_fin]
      field_simp
    have col_is_eq : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = zeroed_row_col ⟨index.1, by omega⟩ col' := by
      intro col' col_neq
      rw [eq', zeroOutColMatrix_lemma, Matrix.of_apply]
      simp
    apply Or.elim roworcol
    . intro rowltind1
      have rowltind: row.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le rowltind)
      . intro roweqind
        have colneqind: col ≠ index := by
          apply Fin.ne_of_val_ne
          rw [← roweqind]
          exact fun a => roweqcol (id (Eq.symm a))
        specialize col_is_eq col colneqind
        rw [eq'] at col_is_eq
        have row_eq_ind_fin : row = ⟨index.1, by omega⟩ := Fin.eq_mk_iff_val_eq.mpr roweqind
        rw [row_eq_ind_fin]
        have simp_N: (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (by omega)) = zeroOutColMatrix' N ⟨index.1, by omega⟩ (by omega) := by
          rw [eq]
          rw [same_zeroOutColMatrix N]
          omega
        rw [← simp_N]
        simp [zeroOutColMatrix_lemma]
        rw [eq]
        simp [zeroOutRowMatrix_lemma, colneqind]
        field_simp
      . intro rowltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        apply pivotMdiag
        . exact Or.inl (by aesop)
        . exact fun h => (by simp_all [N, zeroed_row])
    . intro colltind1
      have colleind : col.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le colleind)
      . intro coleqind
        rw [eq]
        rw [← Matrix.mul_assoc]
        have h : index.1 < numEqns := Nat.gt_of_not_le eqngtind
        set zeroed_col := (zeroOutColMatrix' N ⟨index.1, h⟩ (index.2)) * N with eq'''
        have col_eq_ind_fin : col = index := Fin.eq_of_val_eq coleqind
        have simp_N : zeroOutRowMatrix' zeroed_col index (h) = zeroOutRowMatrix' N index (h) := by
          rw [eq''']
          rw [same_zeroOutRowMatrix N]
        rw [← simp_N]
        simp [zeroOutRowMatrix_lemma, col_eq_ind_fin]
        rw [eq''']
        have row_neq_index : row ≠ ⟨index.1, by omega⟩ := by
          apply Fin.ne_of_val_ne
          rw [← coleqind]
          assumption
        simp [zeroOutColMatrix_lemma, row_neq_index]
        field_simp
      . intro colltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        specialize pivotMdiag row col (by aesop) (by aesop)
        exact pivotMdiag

end ApplyingPivot
