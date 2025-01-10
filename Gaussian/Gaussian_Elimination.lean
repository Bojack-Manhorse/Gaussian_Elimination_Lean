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

/- Function to swap rows `i` and `j`: -/
def swap_row {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : linear_system k n α :=
  ⟨Vector.swap (system.equations) i j⟩
  --⟨Array.swap (system.equations.toArray) i j (by aesop) (by aesop) , by simp⟩

@[simp]
lemma swap_row_defn {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂).equations = Vector.swap (system.equations) i j := by rfl


/- Function to check if some `β : Vector α (n-1)` is a solution to a system of equations: -/
def beta_is_solution {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1)) : Prop :=
  ∀ i < Nat.pred n , eval_poly system.equations[i]! β = 0

theorem row_opr_preserves_sol {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1))
    (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (add_row system coef i j h₁ h₂) β := by
  sorry

@[simp]
lemma vector_index_eq_array_index {k : ℕ} {α : Type} (vec : Vector α k) (i : ℕ) (hi : i < k)
    : vec[i]'(hi) = vec.toArray[i]'(by aesop) := by rfl

@[simp]
lemma swap_to_array_comm {k : ℕ} {α : Type} (vec : Vector α k) (i j : ℕ) (hi : i < k) (hj : j < k)
    : (Vector.swap vec i j hi hj).toArray = Array.swap vec.toArray i j (by aesop) (by aesop) := by rfl

@[simp]
lemma swap_vectors_defn {k : ℕ} {α : Type} (vec : Vector α k) (i j : ℕ) (hi : i < k) (hj : j < k)
    : (Vector.swap vec i j hi hj)[i]'(hi) = vec[j]'(hj) := by simp

lemma swap_vectors_same {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂).equations[i]'(h₁) = system.equations[j]'(h₂) := by
  simp

theorem swap_opr_preserves_sol {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1))
    (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (swap_row system i j h₁ h₂) β := by
  intro h
  rw [beta_is_solution] at *
  intro i ileqn
  rw [swap_row_defn]


end Elimination
