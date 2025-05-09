import Gaussian.Matrix.Diagonalise.PivotFunctions
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section SwapLemmas

lemma same_swap_identity_1 (i : Fin numEqns) : swapRowMatrix i i = (1 : Matrix (Fin numEqns) (Fin numEqns) α) := by
  ext row col
  simp [swapRowMatrix, Matrix.stdBasisMatrix]
  aesop

lemma same_swap_identity_2 (i : Fin numVars) : swapColMatrix i i = (1 : Matrix (Fin numVars) (Fin numVars) α) := by
  ext row col
  simp [swapColMatrix, Matrix.stdBasisMatrix]
  aesop

/- The next two lemmas assert that the result from applying `makeNonZeroAtDiag` will always be a swap row/column matrix. -/

lemma only_swaps_or_indentity_from_makeNonZeroAtDiag_right
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : (∃ i j : Fin numEqns, (makeNonZeroAtDiag M index).1 = swapRowMatrix i j ∧ (index.1 ≤ i.1 ∧ index.1 ≤ j.1)) ∨ (makeNonZeroAtDiag M index).1 = 1 := by
  rw [makeNonZeroAtDiag]
  by_cases indeqns : numEqns ≤ index
  . simp [indeqns]
  . simp [indeqns]
    set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
    by_cases M_zero : M ⟨↑index, by omega⟩ index = 0
    . simp [M_zero]
      split
      . apply Or.inl
        let list := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
        use list[0].2
        use ⟨index.1, by omega⟩
        have in_list : list[0] ∈ list := List.getElem_mem (by assumption)
        have in_list_prop : _ := List.of_mem_filter in_list
        have : ↑index < list[0].2.1 := by aesop
        simp only [le_refl, and_true, true_and]
        omega
      . aesop
    . aesop

lemma only_swaps_or_indentity_from_makeNonZeroAtDiag_left
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : ∃ i j : Fin numVars, (makeNonZeroAtDiag M index).2 = swapColMatrix i j ∧ (index ≤ i ∧ index ≤ j) := by
  rw [makeNonZeroAtDiag]
  by_cases indeqns : numEqns ≤ index
  . simp_all only [gt_iff_lt, ge_iff_le, ↓reduceDIte, Prod.mk_one_one, Prod.snd_one]
    use index; use index; aesop (add simp same_swap_identity_2)
  . simp only [indeqns, ↓reduceDIte]
    by_cases M_zero : M ⟨↑index, by omega⟩ index ≠ 0
    . simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, ↓reduceDIte, Prod.mk_one_one, Prod.snd_one]
      use index; use index; aesop (add simp same_swap_identity_2)
    . simp only [M_zero, ↓reduceDIte]
      aesop
      . use index; use index; aesop (add simp same_swap_identity_2)
      . let list := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0)) (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x)))
        use list[0].2
        use index
        have in_list : list[0] ∈ list := List.getElem_mem (by assumption)
        have in_list_prop : _ := List.of_mem_filter in_list
        have : index < list[0].2 := by aesop
        simp only [le_refl, and_true, true_and]
        omega
      . use index; use index; aesop (add simp same_swap_identity_2)


/- Proves that a applying a swap operation on rows both greater than equal two `index` preserves the `diagonalOutsideInnerBlock` property. -/
lemma diagonalOutsideInnerBlock_preserved_under_swapRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (i j : Fin numEqns)
    (h₁ : index.1 ≤ i.1) (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock ((swapRowMatrix i j) * M) index := by
  intro row col roworcol rowneqcol
  rw [swapRowMatrix_lemma, Matrix.of_apply]
  by_cases roweqi : row = i
  . simp only [roweqi, ↓reduceIte]
    have : col < index := by omega
    have : j.1 ≠ col.1 := by omega
    aesop
  . simp [roweqi]
    by_cases roweqj : row = j
    . simp [roweqj]
      have : col < index := by omega
      have : i.1 ≠ col.1 := by omega
      aesop
    . aesop

lemma diagonalOutsideInnerBlock_preserved_under_swapRowMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin (numVars + 1))
    (i j : Fin numEqns)
    (h₁ : index.1 ≤ i.1) (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock' M index)
    : diagonalOutsideInnerBlock' ((swapRowMatrix i j) * M) index := by
  rw [diagonalOutsideInnerBlock']
  apply Or.elim (lt_or_eq_of_le (Nat.lt_succ_iff.mp index.2))
  . intro ind_lt_vars
    have neq : ¬ index.1 = numVars := by aesop
    simp only [neq, ↓reduceIte, ne_eq, ↓reduceDIte]
    simp only [diagonalOutsideInnerBlock', neq, ↓reduceIte] at Mdiag
    apply diagonalOutsideInnerBlock_preserved_under_swapRowMatrix <;> aesop
  . intro ind_eq_vars
    have eq : index.1 = numVars := by aesop
    simp only [eq, ↓reduceDIte, diagonalOutsideInnerBlock'] at *
    rw [isDiagonal]
    intro row col roworcol
    rw [swapRowMatrix_lemma, Matrix.of_apply]
    split
    . have : j.1 > col := by omega
      have : j.1 ≠ col := by omega
      apply Mdiag
      assumption
    . split
      . have : i.1 > col := by omega
        have : i.1 ≠ col := by omega
        apply Mdiag
        assumption
      . apply Mdiag
        assumption

/- Same as above but with column operations. -/
lemma diagonalOutsideInnerBlock_preserved_under_swapColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (i j : Fin numVars)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (swapColMatrix i j)) index := by
  intro row col roworcol rowneqcol
  rw [swapColMatrix_lemma, Matrix.of_apply]
  by_cases coleqi : col = i
  . simp only [coleqi, ↓reduceIte]
    have : row < index.1 := by omega
    have : j.1 ≠ row.1 := by omega
    aesop
  . simp [coleqi]
    by_cases coleqj : col = j
    . simp [coleqj]
      have : row < index.1 := by omega
      have : i.1 ≠ row.1 := by omega
      aesop
    . aesop

lemma diagonalOutsideInnerBlock_preserved_under_swapColMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin (numVars + 1))
    (i j : Fin numVars)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock' M index)
    : diagonalOutsideInnerBlock' (M * (swapColMatrix i j)) index := by
  rw [diagonalOutsideInnerBlock']
  apply Or.elim (lt_or_eq_of_le (Nat.lt_succ_iff.mp index.2))
  . intro ind_lt_vars
    have neq : ¬ index.1 = numVars := by aesop
    simp only [neq, ↓reduceIte, ne_eq, ↓reduceDIte]
    simp only [diagonalOutsideInnerBlock', neq, ↓reduceIte] at Mdiag
    apply diagonalOutsideInnerBlock_preserved_under_swapColMatrix <;> aesop
  . intro ind_eq_vars
    have eq : index = ↑numVars := by aesop
    simp [eq, diagonalOutsideInnerBlock'] at *
    have : ¬ i.1 < numVars := by omega
    have : i.1 < numVars := i.2
    contradiction

/- If we apply `makeNonZeroAtDiag` to a matrix `M`, then it preserves the `diagonalOutsideInnerBlock` property. -/
lemma diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : let pair := makeNonZeroAtDiag M index;
      diagonalOutsideInnerBlock (pair.1 * M * pair.2) index := by
  intro pair
  aesop
  have row_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_right M index
  obtain ⟨i_row, j_row, h_row⟩ := row_assumption
  . have col_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_left M index
    obtain ⟨i_col, j_col, h_col⟩ := col_assumption
    rw [h_row.1, h_col.1]
    have row_diag : diagonalOutsideInnerBlock (swapRowMatrix i_row j_row * M) index := by
      refine diagonalOutsideInnerBlock_preserved_under_swapRowMatrix M index i_row j_row ?_ ?_ Mdiag
      . aesop
      . aesop
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_swapColMatrix)
  . aesop
    have col_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_left M index
    obtain ⟨i_col, j_col, h_col⟩ := col_assumption
    rw [h_col.1]
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_swapColMatrix)

lemma list_with_index_fin {β : Type} {f : Fin numEqns → β} {a : β × (Fin numEqns)}
    (a_in_list : a ∈ List.ofFn (fun x : Fin numEqns => (f x, x)))
    : a = (f a.2, a.2) := by
  obtain ⟨x, h⟩ := (List.mem_ofFn _ a).mp a_in_list
  apply Prod.fst_eq_iff.mp
  subst h
  simp_all only

/- If there exists some non-zero element on the row and column intersecting `M index index`, then after applying makeNonZeroAtDiag, we'll have a non-zero element at `M index index`. -/
/- Lots of boilerplate code!! Will fix later haha. -/
lemma zero_after_makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqn : index.1 < numEqns)
    (exists_non_zero : ¬ ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0)
    : ((makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2) ⟨index.1, by omega⟩ index ≠ 0 := by
  push_neg at exists_non_zero
  obtain ⟨row, col, ⟨⟨rowgeind, colgeind, roworcol⟩, Mrowcol⟩⟩ := exists_non_zero
  rw [makeNonZeroAtDiag]
  have indlteqn' : ¬ index.1 ≥ numEqns := by omega
  simp [indlteqn']
  by_cases Mzero : M ⟨index.1, by omega⟩ index = 0
  . simp [Mzero]
    have colorrow : col.1 = index.1 ∨ row.1 = index.1 := by aesop
    apply Or.elim colorrow
    . intro coleqind
      have : row.1 ≠ index.1 := by
        by_contra roweqind;
        have : M row col ≠ 0 := by assumption
        have : row = ⟨index.1, by omega⟩ := by aesop
        have : col = ⟨index.1, by omega⟩ := by aesop
        have : M row col = 0 := by aesop
        aesop
      set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
      have coleqind_fin: col = ⟨index.1, by omega⟩ := by aesop
      have : (M row ⟨index.1, by omega⟩, row) ∈ (List.ofFn fun x => (M x index, x)) := list_ofFn_mem rfl
      have : row.1 > index.1 := by omega
      have : (M row ⟨index.1, by omega⟩, row) ∈ ls := by aesop
      have ls_len : ls.length > 0 := List.length_pos_of_mem this
      simp [ls_len]
      simp [swapRowMatrix_lemma, Matrix.of_apply]
      set swap_col := ls[0] with eq
      have swap_in_filter : swap_col ∈ ls := by aesop
      let f : α × (Fin numEqns) → Bool := fun x => decide (index.1 < ↑x.2) && !decide (x.1 = 0)
      have : f swap_col := List.of_mem_filter swap_in_filter
      have : swap_col.1 ≠ 0 := by aesop
      have : swap_col.2 ≠ ⟨index.1, by omega⟩ := by aesop
      have swapgtind : ⟨index.1, by omega⟩ ≠ swap_col.2  := by aesop
      simp [swapgtind]
      rw [← ne_eq]
      set g : (Fin numEqns) → α := fun x => M x index with eq
      have swap_in_list : swap_col ∈ (List.ofFn fun x => (g x, x)) := List.mem_of_mem_filter swap_in_filter
      have swap_col_value : swap_col = (g swap_col.2 , swap_col.2) := list_with_index_fin swap_in_list
      simp [g] at swap_col_value
      have : swap_col.1 = M swap_col.2 index := Prod.fst_eq_iff.mpr swap_col_value
      rw [← this]
      assumption
    . intro roweqind
      have : col.1 ≠ index := by
        by_contra coleqind
        have : M row col ≠ 0 := by assumption
        have : row = ⟨index.1, by omega⟩ := by aesop
        have : col = ⟨index.1, by omega⟩ := by aesop
        have : M row col = 0 := by aesop
        aesop
      set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
      by_cases ls_len : ls.length > 0
      . set swap_col := ls[0]
        simp [ls_len]
        simp [swapRowMatrix_lemma, Matrix.of_apply]
        have swap_in_filter : swap_col ∈ ls := by aesop
        let f : α × (Fin numEqns) → Bool := fun x => decide (index.1 < ↑x.2) && !decide (x.1 = 0)
        have : f swap_col := List.of_mem_filter swap_in_filter
        have : swap_col.1 ≠ 0 := by aesop
        have : swap_col.2 ≠ ⟨index.1, by omega⟩ := by aesop
        have swapgtind : ⟨index.1, by omega⟩ ≠ swap_col.2  := by aesop
        simp [swapgtind]
        rw [← ne_eq]
        set g : (Fin numEqns) → α := fun x => M x index with eq
        have swap_in_list : swap_col ∈ (List.ofFn fun x => (g x, x)) := List.mem_of_mem_filter swap_in_filter
        have swap_col_value : swap_col = (g swap_col.2 , swap_col.2) := list_with_index_fin swap_in_list
        simp [g] at swap_col_value
        have : swap_col.1 = M swap_col.2 index := Prod.fst_eq_iff.mpr swap_col_value
        rw [← this]
        assumption
      . simp [ls_len]
        have roweqind_fin : row = ⟨index.1, by omega⟩ := by aesop
        set swap_row := (M ⟨index.1, by omega⟩ col, col)
        have : swap_row ∈ (List.ofFn fun x => (M ⟨index.1, by omega⟩ x, x)) := list_ofFn_mem rfl
        set ls' := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0)) (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x))) with ls'_eq
        have : col.1 > index.1 := by omega
        have swap_row_in_ls' : swap_row ∈ ls' := by aesop
        have ls'_length: ls'.length > 0 := by exact List.length_pos_of_mem swap_row_in_ls'
        simp [ls'_length]
        set swap_row_first := ls'[0]
        have swap_row_first_in_ls' : swap_row_first ∈ ls' := by aesop
        simp [swapColMatrix_lemma, Matrix.of_apply]
        set f : α × (Fin numVars) → Bool := fun x => decide (index < x.2) && !decide (x.1 = 0) with eq_f
        have : f swap_row_first := by
          rw [ls'_eq] at swap_row_in_ls'
          apply List.of_mem_filter
          exact swap_row_first_in_ls'
        have : swap_row_first.1 ≠ 0 := by aesop
        have : index.1 < swap_row_first.2 := by aesop
        have : index.1 ≠ swap_row_first.2 := by omega
        have swap_neq : index ≠ swap_row_first.2 := fun a => this (congrArg Fin.val a)
        simp [swap_neq]
        set g : (Fin numVars) → α := fun x => M ⟨index.1, by omega⟩ x with eq
        set ls₀ := (List.ofFn (fun x => (g x, x)))
        have : swap_row_first ∈ ls₀ := List.mem_of_mem_filter swap_row_first_in_ls'
        have swap_row_first_as_g : swap_row_first = (g swap_row_first.2, swap_row_first.2) := by
          apply list_with_index_fin
          aesop
        have : swap_row_first.1 = M ⟨index.1, by omega⟩ swap_row_first.2 := by
          apply Prod.fst_eq_iff.mpr
          rw [swap_row_first_as_g]
        rw [← this]
        assumption
  . simp [Mzero]

end SwapLemmas
