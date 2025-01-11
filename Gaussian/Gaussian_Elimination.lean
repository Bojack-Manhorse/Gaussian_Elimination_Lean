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

@[simp]
lemma add_row_1 {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂).equations[j].coefficients = ((Array.set (system.equations.toArray) j (system.equations[j]'(by aesop) + coef • system.equations[i]'(by aesop)) (by aesop))[j]'(by simpa)).coefficients := by rfl

@[simp]
lemma add_row_defn {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : ((add_row system coef i j h₁ h₂).equations[j]'(by aesop)).coefficients = (system.equations[j]'(by aesop) + coef • system.equations[i]'(by aesop)).coefficients := by
  simp --[add_row_1, Array.getElem_set]

@[simp]
lemma add_row_same_index {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂).equations[j]'(h₂) = system.equations[j]'(h₂) + coef • system.equations[i]'(h₁) := by
  apply linear_equation.ext_iff.mpr
  simp

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
  ∀ i : Fin ↑k  , eval_poly (system.equations[i.1]'(i.2)) β = 0


theorem add_opr_preserves_sol {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1))
    (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (add_row system coef i j h₁ h₂) β := by
  repeat rw [beta_is_solution]
  intro h index
  apply Or.elim (eq_or_ne (index.1) j)
  . intro indeqj
    simp only [indeqj, add_row_same_index, eval_poly]
    simp only [Fin.getElem_fin]
  . intro indneqi
    simp
    sorry



@[simp]
lemma vec_eq_index {k : ℕ} {α : Type} (vec : Vector α k) (i : ℕ) (index : Fin k) (h : ↑index = i) : vec[index.1] = vec[i] := by simp [h]

@[simp]
lemma vector_index_eq_array_index {k : ℕ} {α : Type} (vec : Vector α k) (i : ℕ) (hi : i < k)
    : vec[i]'(hi) = vec.toArray[i]'(by aesop) := by rfl

@[simp]
lemma swap_to_array_comm {k : ℕ} {α : Type} (vec : Vector α k) (i j : ℕ) (hi : i < k) (hj : j < k)
    : (Vector.swap vec i j hi hj).toArray = Array.swap vec.toArray i j (by aesop) (by aesop) := by rfl

@[simp]
lemma swap_vectors_defn {k : ℕ} {α : Type} (vec : Vector α k) (i j : ℕ) (hi : i < k) (hj : j < k)
    : (Vector.swap vec i j hi hj)[i]'(hi) = vec[j]'(hj) := by simp

@[simp]
lemma swap_vectors_same {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂).equations[i] = system.equations[j] := by
  simp

@[simp]
lemma swap_vectors_same_right {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂).equations[j] = system.equations[i] := by
  simp

@[simp]
lemma swap_vectors_no_change {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) (index : Fin k) (h₃ : ↑index ≠ i) (h₄ : ↑index ≠ j)
    : (swap_row system i j h₁ h₂).equations[index.1] = system.equations[index.1] := by
  refine linear_equation.ext_iff.mpr ?_
  simp [Array.getElem_swap, h₃, h₄]

theorem swap_opr_preserves_sol {k n : {x : ℕ // x > 1}} {α : Type} [Field α] [Inhabited α] [Inhabited (linear_equation n α)]
    (system : linear_system k n α) (β : Vector α (n - 1))
    (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (swap_row system i j h₁ h₂) β := by
  intro h
  rw [beta_is_solution] at *
  intro index
  apply Or.elim (eq_or_ne (index.1) i)
  . intro indeqi
    rw [vec_eq_index (swap_row system i j h₁ h₂).equations i index indeqi, swap_vectors_same]
    exact h ⟨j, h₂⟩
  . intro indneqi
    apply Or.elim (eq_or_ne (index.1) j)
    . intro indeqj
      rw [vec_eq_index (swap_row system i j h₁ h₂).equations j index indeqj, swap_vectors_same_right]
      exact h ⟨i, h₁⟩
    . intro indneqj
      rw [swap_vectors_no_change system i j h₁ h₂ index indneqi indneqj]
      exact h ↑index





end Elimination
