import Gaussian.Group_Structure

namespace Elimination

open LinearEquation

abbrev linearSystem (α : Type) [Field α] [Inhabited α] (num_eqns num_vars : ℕ) :=
  Vector (linear_equation num_vars α) num_eqns

variable {α : Type} [Field α] [Inhabited α] {k n : {x : ℕ // x > 1}}

instance [Inhabited α] : Inhabited (linear_equation n α) :=
  ⟨{coefficients := Array.replicate n default, length := by simp}⟩

/- Function to add `coef * row i` to `row j`: -/
def add_row (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : linearSystem α k n :=
  ⟨Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop) , by simp⟩

@[simp]
lemma add_row_1 (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j].coefficients = ((Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop))[j]'(by simpa)).coefficients := by rfl

@[simp]
lemma add_row_defn (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : ((add_row system coef i j h₁ h₂)[j]'(by aesop)).coefficients = (system[j]'(by aesop) + coef • system[i]'(by aesop)).coefficients := by
  simp --[add_row_1, Array.getElem_set]

@[simp]
lemma add_row_same_index (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j]'(h₂) = system[j]'(h₂) + coef • system[i]'(h₁) := by
  apply linear_equation.ext_iff.mpr
  simp

/- Function to swap rows `i` and `j`: -/
def swap_row (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : linearSystem α k n :=
  Vector.swap system i j
  --⟨Array.swap (system.toArray) i j (by aesop) (by aesop) , by simp⟩

@[simp]
lemma swap_row_defn (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂) = Vector.swap (system) i j := by rfl


/- Function to check if some `β : Vector α (n-1)` is a solution to a system of equations: -/
def beta_is_solution (system : linearSystem α k n) (β : Vector α (n - 1)) : Prop :=
  ∀ i : Fin ↑k  , eval_poly (system[i.1]'(i.2)) β = 0

theorem add_opr_preserves_sol (system : linearSystem α k n) (β : Vector α (n - 1))
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
lemma vec_eq_index {l : ℕ} {β : Type} (vec : Vector β l) (i : ℕ) (index : Fin l) (h : ↑index = i) : vec[index.1] = vec[i] := by simp [h]

@[simp]
lemma vector_index_eq_array_index {l : ℕ} {β : Type} (vec : Vector β l) (i : ℕ) (hi : i < l)
    : vec[i]'(hi) = vec.toArray[i]'(by aesop) := by rfl

@[simp]
lemma swap_to_array_comm {l : ℕ} {β : Type} (vec : Vector β l) (i j : ℕ) (hi : i < l) (hj : j < l)
    : (Vector.swap vec i j hi hj).toArray = Array.swap vec.toArray i j (by aesop) (by aesop) := by rfl

@[simp]
lemma swap_vectors_defn {l : ℕ} {β : Type} (vec : Vector β l) (i j : ℕ) (hi : i < l) (hj : j < l)
    : (Vector.swap vec i j hi hj)[i]'(hi) = vec[j]'(hj) := by simp

@[simp]
lemma swap_vectors_same (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂)[i] = system[j] := by
  simp

@[simp]
lemma swap_vectors_same_right (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂)[j] = system[i] := by
  simp

@[simp]
lemma swap_vectors_no_change (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) (index : Fin k) (h₃ : ↑index ≠ i) (h₄ : ↑index ≠ j)
    : (swap_row system i j h₁ h₂)[index.1] = system[index.1] := by
  refine linear_equation.ext_iff.mpr ?_
  simp [Array.getElem_swap, h₃, h₄]

theorem swap_opr_preserves_sol (system : linearSystem α k n) (β : Vector α (n - 1))
    (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (swap_row system i j h₁ h₂) β := by
  intro h
  rw [beta_is_solution] at *
  intro index
  apply Or.elim (eq_or_ne (index.1) i)
  . intro indeqi
    rw [vec_eq_index (swap_row system i j h₁ h₂) i index indeqi, swap_vectors_same]
    exact h ⟨j, h₂⟩
    /- For some random reason lean wants me to give natural numbers bigger than one?-/
    exact ⟨2, by norm_num⟩
    exact ⟨2, by norm_num⟩
  . intro indneqi
    apply Or.elim (eq_or_ne (index.1) j)
    . intro indeqj
      rw [vec_eq_index (swap_row system i j h₁ h₂) j index indeqj, swap_vectors_same_right]
      exact h ⟨i, h₁⟩
      /- Same as above??!!-/
      exact ⟨2, by norm_num⟩
      exact ⟨2, by norm_num⟩
    . intro indneqj
      rw [swap_vectors_no_change system i j h₁ h₂ index indneqi indneqj]
      exact h ↑index





end Elimination
