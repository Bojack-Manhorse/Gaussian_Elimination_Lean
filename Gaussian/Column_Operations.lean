import Gaussian.Row_Operations

namespace ColumnOperations

open GroupStructure

open LinearEquation

open RowOperations

variable {α : Type} [Field α] [Inhabited α] {k n : {x : ℕ  // x > 1}}

instance [Inhabited α] : Inhabited (linearEquation α n) :=
  ⟨Array.replicate n default, by simp [Array.size]⟩

def change_var_add_eqn {i j : ℕ} (h₁ : i < n - 1) (h₂ : j < n - 1) (coef : α)  (eqn : linearEquation α n ): linearEquation α n :=
  eqn.set j (eqn[j] + coef * eqn[i])

def change_var_add_vec {i j : ℕ} (h₁ : i < n - 1) (h₂ : j < n - 1) (coef : α) (β : Vector α (n - 1)) : Vector α (n - 1) :=
  β.set j (β[j] + coef * β[i])

def add_column (system : linearSystem α k n) (i j : ℕ)  (h₁ : i < n - 1) (h₂ : j < n - 1) (coef : α) : linearSystem α k n :=
  system.map (fun eqn => @change_var_add_eqn _ _ _ k n i j h₁ h₂ coef eqn)

def change_var_swap {i j : ℕ} (h₁ : i < n - 1) (h₂ : j < n - 1) : linearEquation α n → linearEquation α n := fun eqn : linearEquation α n => eqn.swap i j

def swap_column (system : linearSystem α k n) {i j : ℕ} (h₁ : i < n - 1) (h₂ : j < n - 1) : linearSystem α k n :=
  system.map (@change_var_swap _ _ _ k n i j h₁ h₂)

theorem change_var_add_preserves_sol (system : linearSystem α k n) {i j : ℕ} (h₁ : i < n - 1) (h₂ : j < n - 1) (coef : α) (β : Vector α (n - 1))
    : (beta_is_solution system β) → beta_is_solution (add_column system i j h₁ h₂ coef) (change_var_add_vec h₁ h₂ coef β) := by
  intro original_sol
  rw [beta_is_solution] at *
  intro i
  simp only [change_var_add_vec, add_column, eval_poly]



end ColumnOperations
