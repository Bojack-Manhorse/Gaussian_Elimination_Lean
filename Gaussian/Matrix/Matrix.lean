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

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
def is_false_diagonal (system : @linearSystem α num_vars num_eqns) (h : is_diagonal system.vars) : Bool :=
  let parity_check := List.ofFn (fun i : Fin (min num_eqns num_vars) =>
    let i_eqn : Fin (num_eqns) := ⟨i.1, by omega⟩
    let i_vars : Fin (num_vars) := ⟨i.1, by omega⟩
    (system.vars i_eqn i_vars, system.const i_eqn 1 / system.const i_eqn 1))
  (0, 1) ∈ parity_check

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

/- Check that the solution from `get_sol_diagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (system : @linearSystem α num_vars num_eqns ) (h1 : is_diagonal system.vars) (h2 : ¬ is_false_diagonal system h1)
    : is_sol system (get_sol_diagonal system h1 h2) := by
  rw [is_sol, beq_iff_eq]
  apply Matrix.ext
  intro i j
  sorry

end DiagonalMatrices


end MatrixElimination
