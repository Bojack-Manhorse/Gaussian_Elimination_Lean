import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [Inhabited α] [DecidableEq α]

variable {num_vars num_eqns : ℕ}

section SystemsOfLinearEquations

/- A pair consisting of a `num_eqns × num_vars` matrix and a `num_eqns × 1` matrix that we wish to find some vector of size `num_vars × 1` that's a solution to the pair. -/
structure linearSystem where
  vars : Matrix (Fin num_eqns) (Fin num_vars) α
  const : Matrix (Fin num_eqns) (Fin 1) α

/- Definition of some vector `β` being a solution to some `system : linearSystem`: -/
def is_sol (system : @linearSystem α num_vars num_eqns ) (β : Matrix (Fin num_vars) (Fin 1) α) : Prop :=
  system.vars * β == system.const

end SystemsOfLinearEquations

section Transvections

/- From Mathlib Transvection 78-/
def add_row_transvection (c : α) (i j : Fin num_eqns) : Matrix (Fin num_eqns) (Fin num_eqns) α :=
  1 + Matrix.stdBasisMatrix i j c

/- From Mathlib Transvection 78-/
def add_col_transvection (c : α) (i j : Fin num_vars) : Matrix (Fin num_vars) (Fin num_vars) α :=
  1 + Matrix.stdBasisMatrix i j c

/- A `num_eqns × num_eqns` `P` such that for any matrix `A`, `P * A` represents swapping rows `i, j` of `A`. -/
def swap_row_matrix (i j : Fin num_eqns) : Matrix (Fin num_eqns) (Fin num_eqns) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A `num_vars × num_vars` `P` such that for any matrix `A`, `A * P` represents swapping columns `i, j` of `A`. -/
def swap_col_matrix (i j : Fin num_vars) : Matrix (Fin num_vars) (Fin num_vars) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

end Transvections

section DiagonalMatrices

/- Definition of a `num_eqns × num_vars` being diagonal: -/
def is_diagonal (D : Matrix (Fin num_eqns) (Fin num_vars) α) : Prop :=
  ∀ i : Fin num_eqns, ∀ j : Fin num_vars, (i.1 ≠ j.1 → D i j = 0)

def parity_check_fun (system : @linearSystem α num_vars num_eqns) := (fun i : Fin (num_eqns) =>
    if h1 : i < num_vars then
      let i_vars : Fin (num_vars) := ⟨i.1, by omega⟩
    (system.vars i i_vars, system.const i 1 / system.const i 1)
    else (0, system.const i 1 / system.const i 1)
    )

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
def is_false_diagonal (system : @linearSystem α num_vars num_eqns) (h : is_diagonal system.vars) : Bool :=
  let parity_check := List.ofFn (parity_check_fun system)
  (0, 1) ∈ parity_check

lemma list_ofFn_mem {β : Type} (a : β) (m : ℕ) (f : Fin m → β) (i : Fin m) (aeq : a = f i) : a ∈ List.ofFn f := by
  apply (List.mem_ofFn f a).mpr
  rw [Set.range]
  simp
  exact ⟨i, Eq.symm aeq⟩

example (m l : ℕ) (φ : Prop) (h : if m < l then False else φ) (h2 : m ≥ l) : φ := by
  have h3 : ¬ m < l := Nat.not_lt.mpr h2
  simp at h


lemma cond_for_false {system : @linearSystem α num_vars num_eqns} (h : is_diagonal system.vars) (i : Fin num_eqns)
    : (i ≥ num_vars ∧ system.const i 0 ≠ 0 ) → is_false_diagonal system h := by
  rintro ⟨igeq, cnezero⟩
  rw [is_false_diagonal]
  simp
  refine list_ofFn_mem (0, 1) (num_eqns) _ ?_ ?_
  . exact i
  . have h2 : ¬ i.1 < num_vars := Nat.not_lt.mpr igeq
    rw [parity_check_fun]
    simp [h2]
    field_simp

lemma zero_diag_implies_zero_const {system : @linearSystem α num_vars num_eqns} (h1 : is_diagonal system.vars) (h2 : ¬ is_false_diagonal system h1) (i : Fin num_eqns)
    : (h3 : i < num_vars) → (system.vars i ⟨i.1, by omega⟩ = 0) → (system.const i 0 = 0) := by
  intro h3 h4
  rw [is_false_diagonal] at h2
  simp at h2
  by_contra constneq0
  push_neg at constneq0
  have parity_zero : parity_check_fun system i = (0, 1) := by
    rw [parity_check_fun]
    simp [h3]
    apply And.intro
    . assumption
    . field_simp
  have zero_one_in_list : (0, 1) ∈ List.ofFn (parity_check_fun system) := by
    refine list_ofFn_mem (0, 1) (num_eqns) _ ?_ ?_
    . exact i
    . exact Eq.symm parity_zero
  --pull_neg at h2
  exact h2 zero_one_in_list


/- Verifies that if `is_false_diagonal system h` is true then there are no possible solutions. -/
lemma diagonal_system_has_no_solutions (system : @linearSystem α num_vars num_eqns) (h : is_diagonal system.vars)
    : is_false_diagonal system h ↔ ∀ β : Matrix (Fin num_vars) (Fin 1) α, ¬ is_sol system β := by
  apply Iff.intro
  . sorry
  . sorry



/- Given a system `system` such that `system.vars` is in diagonal form and it has a solution, construct some `β : Matrix (Fin num_vars) (Fin 1) α` that should be a solution (i.e. `system.vars * β == system.const`). -/
def get_sol_diagonal (system : @linearSystem α num_vars num_eqns ) (h1 : is_diagonal system.vars) (h2 : ¬ is_false_diagonal system h1)
    : Matrix (Fin num_vars) (Fin 1) α :=
  Matrix.of
    (fun (i : Fin num_vars) (j : Fin 1) =>
      if eqnsgeqvars : i >= num_eqns then (0 : α)
      else
        let i' : Fin num_eqns  := ⟨i.1, by omega⟩
        (system.const i' 0) / (system.vars i' i)
    )

/- Claimed evaluation of multiplying a diagonal matrix by a vector. -/
def diag_mul_eval (D : Matrix (Fin num_eqns) (Fin num_vars) α) (h : is_diagonal D) (β : Matrix (Fin num_vars) (Fin 1) α) : Matrix (Fin num_eqns) (Fin 1) α :=
    Matrix.of (fun x y =>
    if h : x.1 >= num_vars then 0
    else D x ⟨x.1, by omega⟩ * β ⟨x.1, by omega⟩ y)

/- Verification that `diag_mul_eval` is indeed the actual evaluation. -/
lemma diag_mul_verify (D : Matrix (Fin num_eqns) (Fin num_vars) α) (h : is_diagonal D) (β : Matrix (Fin num_vars) (Fin 1) α)
    : D * β = diag_mul_eval D h β := by
  rw [diag_mul_eval]
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  apply Or.elim (le_or_lt num_vars ↑i)
  . intro igenvars
    have all_zero : ∀ j : Fin (num_vars), D i j * β j k = 0 := by
      intro j
      have D_zero := h i j (by omega)
      simp only [D_zero, zero_mul]
    rw [Fintype.sum_eq_zero _ all_zero]
    simp only [ge_iff_le, Matrix.of_apply, igenvars]
    rfl
  . intro ilenvars
    have inegvars : ¬ num_vars ≤ i := Nat.not_le_of_lt ilenvars
    have all_zero : ∀ j : Fin num_vars, j.1 ≠ i.1 → D i j * β j k = 0 := by
      intro j ineqj
      have D_zero := h i j (id (Ne.symm ineqj))
      simp only [D_zero, zero_mul]
    rw [Fintype.sum_eq_single ⟨i, ilenvars⟩ (fun x neq => all_zero x (Fin.val_ne_of_ne neq))]
    simp only [ge_iff_le, Matrix.of_apply, inegvars, ↓reduceDIte]

/- Check that the solution from `get_sol_diagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (system : @linearSystem α num_vars num_eqns ) (h1 : is_diagonal system.vars) (h2 : ¬ is_false_diagonal system h1)
    : is_sol system (get_sol_diagonal system h1 h2) := by
  rw [is_sol, beq_iff_eq]
  --rw [is_diagonal] at h1
  simp at h2
  rw [diag_mul_verify system.vars h1]
  rw [diag_mul_eval, get_sol_diagonal]
  apply Matrix.ext
  intro i k
  --
  simp
  apply Or.elim (le_or_lt num_vars ↑i)
  . intro igenvars
    simp only [igenvars, ↓reduceDIte]
    have zero : system.const i k = 0 := by
      by_contra h3
      push_neg at h3
      have h5: is_false_diagonal system h1 := by
        apply cond_for_false h1 i
        rw [Fin.fin_one_eq_zero k] at h3
        exact ⟨igenvars, h3⟩
      sorry --exact h5 h2
    rw [zero]
  . intro iltvars
    have h4 : ¬ i ≥ num_vars := Nat.not_le_of_lt iltvars
    simp only [h4, ↓reduceDIte]
    have : ¬ num_eqns ≤ i := Nat.not_le_of_lt i.2
    simp [Nat.not_le_of_lt i.2]
    apply Or.elim (eq_or_ne (system.vars i ⟨i.1, by omega⟩) 0)
    . intro syseq0
      rw [syseq0]
      ring
      rw [Fin.fin_one_eq_zero k]
      apply Eq.symm
      apply zero_diag_implies_zero_const h1 _ i iltvars syseq0
      assumption
    . intro sysneq0
      field_simp
      rw [Fin.fin_one_eq_zero k] at *

end DiagonalMatrices


end MatrixElimination
