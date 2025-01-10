import Gaussian.Group_Structure

namespace Elimination

open LinearEquation

/--
Allowing 0/1-linear systems is beneficial as it removes the dependent type in the definition of the structure.

Furthermore, `abbrev linear_system` (much like `def`) gives us more freebies than a structure.

Furthermore, if you look at e.g. vector, it is customary types go first, so α ... then `num_eqn`.
-/
abbrev linear_system (α : Type) [Field α] [Inhabited α] (num_eqns num_vars : ℕ) :=
  Vector (linear_equation num_vars α) num_eqns

section

/-
So we don't need to repeat this over and over.
-/
variable {α : Type} [Field α] [Inhabited α]
         {k n : ℕ}

/-
We get `Inhabited (linear_equation n α)...` for free because of the abbrev; magic!
-/

/-- Function to add `coef * row i` to `row j`.
    NB I use /-- -/ comment style here to get the information on hovering the definition

    NB minor rename on all of these, customary syntax for defs
-/
def addRow (system : linear_system α k n) (coef : α) (i j : Fin k) :
            linear_system α k n :=
  ⟨system.toArray.set j (system[j] + coef • system[i]) (by aesop), by simp⟩ -- the access syntax system[j] tries a bunch of stuff
                                                                            -- one of which is `assumption`, so `h₁` and `h₂` (bundled in `Fin`s) get
                                                                            -- picked up for free, no need for system[j]'proof

/- Function to swap rows `i` and `j`: -/
def swapRow (system : linear_system α k n) (i j : Fin k) : linear_system α k n :=
  system.swap i j
  --⟨Array.swap (system.equations.toArray) i j (by aesop) (by aesop) , by simp⟩

@[simp]
lemma swapRow_defn {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
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

end

end Elimination
