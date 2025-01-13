import Gaussian.Group_Structure
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 1000000

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
lemma add_row_first_defn (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂).toArray = Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop) := by rfl

@[simp]
lemma add_row_1 (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j].coefficients = ((Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop))[j]'(by simpa)).coefficients := by rfl

@[simp]
lemma add_row_2 (system : linearSystem α k n) (coef : α) (i j index : ℕ) (h₁ : i < k) (h₂ : j < k) (h₃ : index < k) (h₄ : index ≠ j)
    : (add_row system coef i j h₁ h₂)[index].coefficients = ((Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop))[index]'(by simpa)).coefficients := by rfl

@[simp]
lemma add_row_defn (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : ((add_row system coef i j h₁ h₂)[j]'(by aesop)).coefficients = (system[j]'(by aesop) + coef • system[i]'(by aesop)).coefficients := by
  simp --[add_row_1, Array.getElem_set]

@[simp]
lemma add_row_same_index (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j]'(h₂) = system[j]'(h₂) + coef • system[i]'(h₁) := by
  apply linear_equation.ext_iff.mpr
  simp only [add_row_1, Array.getElem_set_eq, defn_of_add_no_index, GroupStructure.defn_of_smul]

@[simp]
lemma add_row_diff_index (system : linearSystem α k n) (coef : α) (i j index : ℕ) (h₁ : i < k) (h₂ : j < k) (h₃ : index < k) (h₄ : index ≠ j)
    : (add_row system coef i j h₁ h₂)[index]'(h₃) = system[index]'(h₃) := by
  apply linear_equation.ext_iff.mpr
  rw [add_row_2]
  rw [Array.getElem_set_ne]
  rfl
  . intro jneq
    exact h₄ (id (Eq.symm jneq))
  . exact h₄

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

--@[simp]
/- This is the same as `index_is_linear!!!-/
lemma swap_index_pt (vec1 vec2 : linear_equation n α) (x : ℕ) (h : x < n) :
    (vec1 + vec2).coefficients[↑x]'(by rw [(vec1 + vec2).length]; exact h) =
    vec1.coefficients[↑x]'(by rw [vec1.length]; exact h) + vec2.coefficients[↑x]'(by rw [vec2.length]; exact h) := by
  apply index_is_linear
  exact h

--@[simp]
lemma swap_scalar_pt (vec : linear_equation n α) (coef : α) (x : ℕ) (h : x < n) :
    (coef • vec).coefficients[x]'(by rw [(coef • vec).length]; exact h ) = coef * (vec.coefficients[x]'(by rw [vec.length]; exact h)) := by
  simp
/-
∑ x : Fin (↑n - 1), β[↑x] * (system[j] + coef • system[i]).coefficients[↑x] +
    (system[j] + coef • system[i]).coefficients[↑n - 1] =
  0
∑ x : Fin (↑n - 1), β[↑x] * (system[j] + coef • system[i]).coefficients[↑x] +
    (system[j] + coef • system[i]).coefficients[↑n - 1] =
  0
-/

lemma fin_less_than (m : {x : ℕ // x > 1}) : ∀ x : Fin (m - 1), ↑x < m.1 := by
  intro x
  apply Nat.lt_trans
  exact x.2
  norm_num
  apply Nat.lt_trans
  exact Nat.zero_lt_one
  exact m.2


theorem add_opr_preserves_sol (system : linearSystem α k n) (β : Vector α (n - 1))
    (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β → beta_is_solution (add_row system coef i j h₁ h₂) β := by
  repeat rw [beta_is_solution]
  intro h index
  apply Or.elim (eq_or_ne (index.1) j)
  . intro indeqj
    simp only [indeqj]
    have h₄ : (add_row system coef i j h₁ h₂)[j] = system[j] + coef • system[i] := by
      simp
    simp only [indeqj, add_row_same_index, eval_poly, Fin.getElem_fin]
    have feqg : ∀ x : Fin (↑n - 1),
        β[x.1] * (system[j] + coef • system[i]).coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x) =
        β[x.1] * (system[j]).coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x)
        + β[x.1] * coef * system[i].coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x) := by
      intro x
      rw [index_is_linear _ _ _ (fin_less_than n x), swap_scalar_pt _ _ _ (fin_less_than n x)]
      ring
    rw [index_is_linear _ _ _ (Nat.sub_one_lt_of_lt n.2), swap_scalar_pt _ _ _ (Nat.sub_one_lt_of_lt n.2)]
    rw [Fintype.sum_congr _ _ feqg, Finset.sum_add_distrib]
    rw [← add_assoc]
    /- I'm so sorry :(-/
    let a₁ := ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * system[j].coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x)
    let a₂ := ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * coef * system[i].coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x)
    let a₃ := system[j].coefficients[↑n - 1]'(by rw [linear_equation.length]; norm_num; exact Nat.lt_trans Nat.zero_lt_one n.2)
    let a₄ := coef * system[i].coefficients[↑n - 1]'(by rw [linear_equation.length]; norm_num; exact Nat.lt_trans Nat.zero_lt_one n.2)
    have ha₁ : a₁ = ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * system[j].coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x) := by rfl
    have ha₂ : a₂ = ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * coef * system[i].coefficients[x.1]'(by rw [linear_equation.length]; exact fin_less_than n x) := by rfl
    have ha₃ : a₃ = system[j].coefficients[↑n - 1]'(by rw [linear_equation.length]; norm_num; exact Nat.lt_trans Nat.zero_lt_one n.2) := by rfl
    have ha₄ : a₄ = coef * system[i].coefficients[↑n - 1]'(by rw [linear_equation.length]; norm_num; exact Nat.lt_trans Nat.zero_lt_one n.2) := by rfl
    rw [← ha₁, ← ha₂, ← ha₃, ← ha₄]

    have h₅ : ∑ x : Fin (↑n - 1), β[↑x] * coef * system[i].coefficients[↑x]'(by rw [linear_equation.length]; exact fin_less_than n x) + coef * system[i].coefficients[↑n - 1]'(by rw [linear_equation.length]; exact Nat.sub_one_lt_of_lt n.2)  = 0 := by
      have my_h : ∑ i_1 : Fin (↑n - 1), β[i_1] * system[i].coefficients[i_1]'(by rw [linear_equation.length]; exact fin_less_than n i_1) + system[i].coefficients[↑n - 1]'(by rw [linear_equation.length]; exact Nat.sub_one_lt_of_lt n.2) = 0 := h ⟨i, h₁⟩
      have sum_comm : ∀ x : Fin (↑n - 1), β[x] * coef * system[i].coefficients[x]'(by rw [linear_equation.length]; exact fin_less_than n x ) = coef * (β[x] * system[i].coefficients[x]'(by rw [linear_equation.length]; exact fin_less_than n x)) := by intro x; ring
      rw [Fintype.sum_congr _ _ (sum_comm)]
      rw [Eq.symm (Finset.mul_sum Finset.univ (fun a : (Fin (↑n - 1)) => (β[a] * system[i].coefficients[a]'(by rw [linear_equation.length]; exact fin_less_than n a ))) coef)]
      rw [← LeftDistribClass.left_distrib coef _ _, my_h]
      ring
    simp at h₅
    rw [← ha₂, ← ha₄] at h₅
    have h₆ : _ := h ⟨j, h₂⟩
    simp at h₆
    rw [← ha₁, ← ha₃] at h₆
    rw [add_assoc a₁ _ _, add_comm a₂ _, ← add_assoc a₁ _, h₆, zero_add, h₅]
  . intro indneqi
    rw [eval_poly]
    rw [add_row_diff_index]
    exact h ↑index
    exact indneqi

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
    /- For some random reason lean wants me to give a natural numbers bigger than one?-/
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
