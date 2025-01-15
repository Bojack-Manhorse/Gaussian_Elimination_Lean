import Gaussian.Group_Structure

namespace RowOperations

open GroupStructure

open LinearEquation

abbrev linearSystem (α : Type) [Field α] [Inhabited α] (num_eqns num_vars : ℕ) :=
  Vector (linearEquation α num_vars) num_eqns

variable {α : Type} [Field α] [Inhabited α] {len k n : {x : ℕ // x > 1}}

instance [Inhabited α] : Inhabited (linearEquation α len) :=
  ⟨Array.replicate len default, by simp [Array.size]⟩

/- Function to add `coef * row i` to `row j`: -/
def add_row (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : linearSystem α k n :=
  ⟨Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop) , by simp⟩

@[simp]
lemma add_row_first_defn (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂).toArray = Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop) := by rfl

@[simp]
lemma add_row_1 (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j].toArray = ((Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop))[j]'(by simpa)).toArray := by rfl

@[simp]
lemma add_row_2 (system : linearSystem α k n) (coef : α) (i j index : ℕ) (h₁ : i < k) (h₂ : j < k) (h₃ : index < k)
    : (add_row system coef i j h₁ h₂)[index].toArray = ((Array.set (system.toArray) j (system[j]'(by aesop) + coef • system[i]'(by aesop)) (by aesop))[index]'(by simpa)).toArray := by rfl

@[simp]
lemma add_row_defn (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : ((add_row system coef i j h₁ h₂)[j]'(by aesop)).toArray = (system[j]'(by aesop) + coef • system[i]'(by aesop)).toArray := by
  simp --[add_row_1, Array.getElem_set]

@[simp]
lemma add_row_same_index (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (add_row system coef i j h₁ h₂)[j]'(h₂) = system[j]'(h₂) + coef • system[i]'(h₁) := by
  apply vector_ext_with_arrays
  simp only [add_row_1, Array.getElem_set_eq, defn_of_add_no_index, GroupStructure.defn_of_smul]

@[simp]
lemma add_row_diff_index (system : linearSystem α k n) (coef : α) (i j index : ℕ) (h₁ : i < k) (h₂ : j < k) (h₃ : index < k) (h₄ : index ≠ j)
    : (add_row system coef i j h₁ h₂)[index]'(h₃) = system[index]'(h₃) := by
  apply vector_ext_with_arrays
  rw [add_row_2]
  rw [Array.getElem_set_ne]
  rfl
  . intro jneq
    exact h₄ (id (Eq.symm jneq))

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
lemma swap_index_pt (vec1 vec2 : linearEquation α n) (x : ℕ) (h : x < n) :
    (vec1 + vec2)[↑x]'(h) =
    vec1[↑x]'(h) + vec2[↑x]'(h) := by
  apply index_is_linear

--@[simp]
lemma swap_scalar_pt (vec : linearEquation α n) (coef : α) (x : ℕ) (h : x < n)
    : (coef • vec)[x]'(h) = coef * (vec[x]'(h)) := by
  rw [← vector_to_array_element, ← vector_to_array_element]
  simp

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
        β[x.1] * (system[j] + coef • system[i])[x.1]'(by omega) =
        β[x.1] * (system[j])[x.1]'(by omega)
        + β[x.1] * coef * system[i][x.1]'(by omega) := by
      intro x
      rw [index_is_linear _ _ _ (fin_less_than n x), swap_scalar_pt _ _ _ (fin_less_than n x)]
      ring
    rw [index_is_linear _ _ _ (Nat.sub_one_lt_of_lt n.2), swap_scalar_pt _ _ _ (Nat.sub_one_lt_of_lt n.2)]
    rw [Fintype.sum_congr _ _ feqg, Finset.sum_add_distrib]
    rw [← add_assoc]
    /- I'm so sorry :(-/
    let a₁ := ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * system[j][x.1]'(by omega)
    let a₂ := ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * coef * system[i][x.1]'(by omega)
    let a₃ := system[j][↑n - 1]'(by omega)
    let a₄ := coef * system[i][↑n - 1]'(by omega)
    have ha₁ : a₁ = ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * system[j][x.1]'(by omega) := by rfl
    have ha₂ : a₂ = ∑ x : Fin (↑n - 1), β[x.1]'(x.2) * coef * system[i][x.1]'(by omega) := by rfl
    have ha₃ : a₃ = system[j][↑n - 1]'(by omega) := by rfl
    have ha₄ : a₄ = coef * system[i][↑n - 1]'(by omega) := by rfl
    rw [← ha₁, ← ha₂, ← ha₃, ← ha₄]

    have h₅ : ∑ x : Fin (↑n - 1), β[↑x] * coef * system[i][↑x]'(by omega) + coef * system[i][↑n - 1]'(by omega) = 0 := by
      have my_h : ∑ i_1 : Fin (↑n - 1), β[i_1] * system[i][i_1]'(by omega) + system[i][↑n - 1]'(by omega) = 0 := h ⟨i, h₁⟩
      have sum_comm : ∀ x : Fin (↑n - 1), β[x] * coef * system[i][x]'(by omega) = coef * (β[x] * system[i][x]'(by omega)) := by intro x; ring
      rw [Fintype.sum_congr _ _ (sum_comm)]
      rw [Eq.symm (Finset.mul_sum Finset.univ (fun a : (Fin (↑n - 1)) => (β[a] * system[i][a]'(by omega))) coef)]
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
lemma reverse_add_operation (system : linearSystem α k n) (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) (ineqj : i ≠ j)
    : add_row (add_row system coef i j h₁ h₂) (-coef) i j h₁ h₂ = system := by
  apply vector_ext
  rintro ⟨index, indlek⟩
  apply Or.elim (eq_or_ne (index) j)
  . intro indeqj
    simp [indeqj]
    rw [add_row_diff_index _ (coef) i j i h₁ h₂ h₁ ineqj, add_assoc, ← Module.add_smul, add_neg_cancel, zero_smul, add_zero]
  . intro indneqj
    rw [add_row_diff_index _ (-coef) i j index h₁ h₂ indlek indneqj]
    rw [add_row_diff_index _ (coef) i j index h₁ h₂ indlek indneqj]

theorem add_opr_preserves_sol_iff (system : linearSystem α k n) (β : Vector α (n - 1))
    (coef : α) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) (ineqj : i ≠ j) :
    beta_is_solution system β ↔ beta_is_solution (add_row system coef i j h₁ h₂) β := by
  apply Iff.intro
  . apply add_opr_preserves_sol
  . intro beta_add
    have g₁ : beta_is_solution (add_row (add_row system (coef) i j h₁ h₂) (-coef) i j h₁ h₂) β := by
      apply add_opr_preserves_sol (add_row system (coef) i j h₁ h₂) β
      exact beta_add
    rw [reverse_add_operation system coef] at g₁
    assumption
    exact ineqj

--@[simp]
lemma vec_eq_index {l : ℕ} {β : Type} (vec : Vector β l) (i : ℕ) (index : Fin l) (h : ↑index = i) : vec[index.1] = vec[i] := by simp [h]

--@[simp]
lemma vector_index_eq_array_index {l : ℕ} {β : Type} (vec : Vector β l) (i : ℕ) (hi : i < l)
    : vec[i]'(hi) = vec.toArray[i]'(by aesop) := by rfl

--@[simp]
lemma swap_to_array_comm {l : ℕ} {β : Type} (vec : Vector β l) (i j : ℕ) (hi : i < l) (hj : j < l)
    : (Vector.swap vec i j hi hj).toArray = Array.swap vec.toArray i j (by aesop) (by aesop) := by rfl

--@[simp]
lemma swap_vectors_defn {l : ℕ} {β : Type} (vec : Vector β l) (i j : ℕ) (hi : i < l) (hj : j < l)
    : (Vector.swap vec i j hi hj)[i]'(hi) = vec[j]'(hj) := by
  simp only [vector_index_eq_array_index, swap_to_array_comm, Array.getElem_swap_left]

--@[simp]
lemma swap_vectors_same (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂)[i] = system[j] := by
  simp only [swap_row_defn, vector_index_eq_array_index, swap_to_array_comm,
    Array.getElem_swap_left]

--@[simp]
lemma swap_vectors_same_right (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k)
    : (swap_row system i j h₁ h₂)[j] = system[i] := by
  simp only [swap_row_defn, vector_index_eq_array_index, swap_to_array_comm,
    Array.getElem_swap_right]

--@[simp]
lemma vector_swap_array {β : Type} {num : ℕ} (p : Vector β num) (i j : ℕ) (h₁ : i < num) (h₂ : j < num) : (Vector.swap p i j h₁ h₂).toArray = Array.swap p.toArray i j (by rw [Vector.size_toArray]; exact h₁) (by rw [Vector.size_toArray]; exact h₂) := by rfl


@[simp]
lemma swap_vectors_no_change (system : linearSystem α k n) (i j : ℕ) (h₁ : i < k) (h₂ : j < k) (index : Fin k) (h₃ : ↑index ≠ i) (h₄ : ↑index ≠ j)
    : (swap_row system i j h₁ h₂)[index.1] = system[index.1] := by
  apply vector_ext_with_arrays
  simp only [swap_row_defn]
  rw [vector_index_eq_array_index]
  simp only [vector_swap_array, Vector.size_toArray, Fin.is_lt, ne_eq, h₃, not_false_eq_true, h₄,
    Array.getElem_swap_of_ne, vector_to_array_element]

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
    exact ⟨2, by norm_num⟩
  . intro indneqi
    apply Or.elim (eq_or_ne (index.1) j)
    . intro indeqj
      rw [vec_eq_index (swap_row system i j h₁ h₂) j index indeqj, swap_vectors_same_right]
      exact h ⟨i, h₁⟩
      /- Same as above??!!-/
      exact ⟨2, by norm_num⟩
      exact ⟨2, by norm_num⟩
      exact ⟨2, by norm_num⟩
    . intro indneqj
      rw [swap_vectors_no_change system i j h₁ h₂ index indneqi indneqj]
      exact h ↑index

lemma double_swap (system : linearSystem α k n)
    (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    swap_row (swap_row system i j h₁ h₂) i j h₁ h₂ = system := by
  apply vector_ext_with_arrays
  simp only [swap_row_defn, swap_to_array_comm, Array.swap_swap]

theorem swap_opr_preserves_sol_iff (system : linearSystem α k n) (β : Vector α (n - 1))
    (i j : ℕ) (h₁ : i < k) (h₂ : j < k) :
    beta_is_solution system β ↔ beta_is_solution (swap_row system i j h₁ h₂) β := by
  apply Iff.intro
  . apply swap_opr_preserves_sol
  . nth_rewrite 2 [← double_swap system i j h₁ h₂]
    apply swap_opr_preserves_sol

end RowOperations
