import Gaussian.Group_Structure

namespace Elimination

open LinearEquation

@[ext]
structure linear_system (num_eqns num_vars : {x : ℕ // x > 1}) (α : Type) [Field α] [Inhabited α] where
  equations : Vector (linear_equation num_vars α) num_eqns

/- Function to add `coef * row i` to `row j`: -/
def add_row {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : linear_system k n α :=
  ⟨Array.set (system.equations.toArray) j (system.equations[j]'(by aesop) + coef • system.equations[i]'(by aesop)) (by aesop) , by simp ⟩

/- Function to check if some `β : Vector α (n-1)` is a solution to a system of equations: -/
def beta_is_solution {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1)) : Prop :=
  ∀ i < Nat.pred n , eval_poly system.equations[i]! β = 0

theorem row_opr_preserves_sol {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1))
    (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (add_row system coef i j h₁ h₂) β := by
  sorry




end Elimination
