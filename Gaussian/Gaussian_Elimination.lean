import Gaussian.Row_Operations
import Mathlib.Tactic.FieldSimp

namespace Gaussian

open LinearEquation

open RowOperations

/-@[simp]
lemma zero_entry_defn (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₂ : i ≠ j) (h₃ : (system[i]'(Nat.lt_trans h₀ kgeqn))[i]'(h₀) ≠ 0)
        : (zero_entry kgeqn system i j h₀ h₁ h₂ h₃)[j] -/

/- Algorithm

First column:

Find first non-zero entry on first column - i


**
do swap system i 0

    for j in range[1, k]:

        coef :=  - system[j][0] / system[0][0]

        do addrow system (coef) 0 j

        show system[j][0] = 0, solution preserved
**

Repeat for columns 1 to n, reaplace 0 with column number, replace j in range [1, k] with j in range [column_num, k]

Write a separate function that applies the ** operation

Iterate over l : [0, min(num_vars, num_eqns)]:

For each l : Check system[l][l] ≠ 0
    If it is, find some j such that system[j][l] ≠ 0
    so swap system j l
    If none exist, skip column?
        Rank system is smaller

    Then do **

-- Get system' in almost diagonal form
-- Read off solution of system', β
-- Show β is a solution of system' => β is a solution of system

Have a representation thats of the form Fin num_rows → Fun num_columns → α

-/

variable {α : Type} [Field α] [DecidableEq α] [Inhabited α] {k n : {x : ℕ // x > 1}} (kgtn : k > n) -- (i j : ℕ) (h₁ : i < n) (h₂ : j < k)

def iltk (i : ℕ) (h : i < n.1) : i < k := Nat.lt_trans h kgtn

/- Assuming `system[i][i] ≠ 0` makes `system[j][i] = 0`: -/

def zero_entry (system : linearSystem α k n) (i j : ℕ ) (h₀ : i < n) (h₁ : j < k) : linearSystem α k n :=
    let coef := -(system[j][i] / (system[i]'(Nat.lt_trans h₀ kgtn))[i])
    add_row system coef i j (Nat.lt_trans h₀ kgtn) h₁

#check zero_entry
#check @zero_entry Nat

lemma zero_entry_after_zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < ↑n) (h₁ : j < ↑k) (h₃ : (system[i]'(Nat.lt_trans h₀ kgtn))[i]'(h₀) ≠ 0) : ((zero_entry kgtn system i j h₀ h₁)[j]'(h₁))[i]'(h₀) = 0 := by
    simp [zero_entry]
    rw [zip_index_pick_fst _ _ (by simp) (by simp) i (h₀), zip_index_pick_snd _ _ (by simp) (by simp) i (h₀)]
    simp only [Array.getElem_map]
    rw [vector_to_array_element _ _ h₀, vector_to_array_element _ _ h₀]
    field_simp

lemma i_th_index_stays_non_zero (system : linearSystem α k n) (i j : ℕ) (h₀ : i < ↑n) (h₁ : j < ↑k) (h₂ : i ≠ j) : (system[i]'(Nat.lt_trans h₀ kgtn))[i]'(h₀) ≠ 0 → ((zero_entry kgtn system i j h₀ h₁)[i]'(lt_trans h₀ kgtn))[i]'(h₀) ≠ 0 := by
    intro sysneq0
    rw [zero_entry, add_row_diff_index]
    exact sysneq0
    exact h₂

structure system_non_zero_i_pair (i : ℕ) (h₀ : i < n) where
    system : linearSystem α k n
    non_zero_i : (system[i]'(Nat.lt_trans h₀ kgtn))[i]'(h₀) ≠ 0

/- Applies `zero_entry` to system_pair using `i_th_index_stays_non_zero`-/
def zero_entry_pair (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₂ : i ≠ j)
        (system_pair : system_non_zero_i_pair (α := α) kgtn i h₀) : (system_non_zero_i_pair (α := α) kgtn i h₀) :=
    ⟨zero_entry kgtn system_pair.system i j h₀ h₁, i_th_index_stays_non_zero kgtn system_pair.system i j h₀ h₁ h₂ system_pair.non_zero_i⟩

/- The function we fold over in `pivot_system_above`: -/
def fold_func_i (i : ℕ) (h₁ : i < n) := fun (system : (linearSystem α k n)) (x : Fin i) => zero_entry kgtn system i x h₁ (Nat.lt_trans x.2 (Nat.lt_trans h₁ kgtn))

def pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) :=
    Fin.foldl i (fold_func_i kgtn i h₁) system

lemma fold_l_swap' {β : Type} (n : ℕ) (f : β → ℕ → β) (b : β) : Fin.foldl (n + 1) (fun x y => f x y) b = f (Fin.foldl n (fun x y => f x y ) b) n := by
    induction' n with i ih
    .   rfl
    .   rw [Fin.foldl, Fin.foldl.loop]
        simp
        rw [ih]
        sorry


lemma zero_above_pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (system[i]'(Nat.lt_trans h₁ kgtn))[i] ≠ 0 → ∀ eqn : Fin i, ((pivot_system_above kgtn system i h₁)[eqn]'(Nat.lt_trans (Nat.lt_trans eqn.2 h₁) kgtn))[i]'(h₁) = 0 := by
    intro sysneq0
    intro eqn
    rw [pivot_system_above]
    /-Use generalizing `system'` maybe?-/
    induction' i  with i ih --generalizing system
    .   rcases eqn; omega
    .   rw [Fin.foldl_succ_last]
        sorry

def pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) :=
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    have h₈ (x : Fin (k - i - 1)) : x.1 + ↑i + 1 < ↑k := by
        rw [add_assoc]
        apply Nat.add_lt_of_lt_sub
        exact x.isLt
    Fin.foldr (k - i - 1) (fun (x : Fin (k - i - 1)) (system' : (linearSystem α k n)) => zero_entry kgtn system' i (x + i + 1) h₁ (h₈ x) ) system

lemma zero_below_pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n)
        : (system[i]'(Nat.lt_trans h₁ kgtn))[i] ≠ 0 → ∀ eqn : Fin (k - i - 1), ((pivot_system_below kgtn system i h₁)[eqn + i - 1])[i]'(h₁) = 0 := sorry

lemma array_to_list_membership {β : Type} (as : Array β) (x : β) : x ∈ as → x ∈ as.toList := by
    exact fun a =>
    a.val

lemma array_range_inequal {x m : ℕ} (h: x ∈ Array.range m ) :  x < m := by
    have h₂ : x ∈ (Array.range m).toList := array_to_list_membership (Array.range m) x h
    have h₃ : x ∈ List.range m := by rw [Array.toList_range] at h₂; exact h₂
    apply List.mem_range.mp
    exact h₃

def index_array_with_proof (m : ℕ) : List (Σ' x : ℕ, x < m) :=
    (List.range m).attach.map (fun x : {x : ℕ // x ∈ List.range m} => ⟨x.1, List.mem_range.mp x.2⟩)

def index_array_with_proof' (m : ℕ) : Array (Fin m) := Array.finRange m


/- Makes the entry at `system[i][i]` non-zero -/
def ensure_non_zero_at_i (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : linearSystem α k n :=
    /- Only look below the `i-th` column when looking for non-zero element -/
    /- Add row and column function.-/
    let entire_i_th_column : Array α := system.toArray.map (fun lin_eqn => lin_eqn[i]'(h₁))

    let entire_i_th_column_zipped : _ := entire_i_th_column.zip (Array.finRange k)

    let i_th_column_below_zipped : _ := entire_i_th_column_zipped.extract i (k + 1)

    let non_zero := Array.filter (fun x => x.1 != 0) i_th_column_below_zipped
    if h : non_zero.size > 0 then
        let index : ℕ := (non_zero[0]'(h)).2
        have indltk : index < ↑k := (non_zero[0]'(h)).2.2
        swap_row system i index (Nat.lt_trans h₁ kgtn) indltk
    else
        system

def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    apply pivot_system_above kgtn _ i h₁
    apply pivot_system_below kgtn _ i h₁
    apply ensure_non_zero_at_i kgtn _ i h₁
    exact system

def row_reduce_system (system : linearSystem α k n) : linearSystem α k n :=
    Fin.foldr n (fun (column : Fin n) (system' : (linearSystem α k n)) => pivot_system kgtn system' column.1 column.2) system

/- Section on various forms of systems e.g. Upper Triangular-/

def system_in_upper_triangular (system : linearSystem α k n) : Prop :=
    ∀ (var : Fin n) (eqn : Fin k), ( eqn.1 > var.1 → ((row_reduce_system kgtn system)[eqn]'(eqn.2))[var]'(var.2) = 0)

lemma upper_triangular_after_row_reduce (system : linearSystem α k n)
        : system_in_upper_triangular kgtn (row_reduce_system kgtn system) := by
    sorry

def system_in_ref (system : linearSystem α k n) : Prop := (system_in_upper_triangular kgtn system) ∧ (∀ i : Fin n, (system[i]'(Nat.lt_trans i.2 kgtn))[i] ≠ 0 → ∀ j : Fin k, system[j][i] = 0)

def system_in_reduced_ref (system : linearSystem α k n) : Prop :=
    ∀ i : Fin (n - 1), (system[i]'(Nat.lt_trans (fin_less_than n i) kgtn))[i] ≠ 0 ∧
    ∀ (i : Fin (n - 1)) (j : Fin k), (i.1 ≠ j.1) → system[j][i] = 0

def system_has_unique_solution (system : linearSystem α k n) : Prop :=
    (∃ β : Vector α (n - 1), beta_is_solution system β ∧ ∀ γ : Vector α (n - 1), beta_is_solution system γ → γ = β)

lemma unique_sol_implies_reduced_ref (system : linearSystem α k n) (unique_sol : system_has_unique_solution system) (rref : system_in_ref kgtn system)
        : (system_in_reduced_ref kgtn system) := by sorry

def get_rank (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) : {x : ℕ // x < n} :=
    let first_n_rows := Array.extract system.toArray 0 n
    have h₁: first_n_rows.size = n := by
        rw [Array.size_extract]
        simp
        apply Nat.le_of_succ_le kgtn
    let rank := (first_n_rows.filter (fun x => x != 0)).size
    have ranklen : rank ≤ ↑n := by
        simp only [← h₁, rank]
        apply Array.size_filter_le
    ⟨rank - 1, by omega⟩

/- Rank row is non-zero -/
lemma non_zero_at_rank (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) : system[(get_rank kgtn system h).1]'(Nat.lt_trans (get_rank kgtn system h).2 kgtn) ≠ 0 := sorry

/- Last row has atleast two non-zero entries, if last entry is non-zero-/
lemma last_row_proper_form (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) (has_sol : ∃ β, beta_is_solution system β) :
        let rank := get_rank kgtn system h
        ∃ index : Fin (n - 1), (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[index] ≠ 0 := sorry

def init_vector : Vector (Option α) (n - 1) := ⟨Array.replicate (n - 1) (none), by simp⟩

instance (v : {x : ℕ // x > 1}) (m : Fin (v - 1)) : Fintype {x : ℕ // x > m.1 ∧ x < v.1} := by
    apply @Fintype.ofInjective {x : ℕ // x > m.1 ∧ x < v.1} (Fin v) _ (fun x => ⟨x.1, x.2.2⟩ : Fin v)
    sorry


/- Given a row of `system` and some vector `β Vector (Option α) (n - 1)`, we fold over this function `n` times to get the solutions from this row: -/
def get_solution_row_fold_func (row : linearEquation α n) : Vector (Option α) (n - 1) → Fin (n - 1) → Vector (Option α) (n - 1) :=
    fun (init : Vector (Option α) (n - 1)) (m : Fin (n - 1)) =>
        if row[m] == 0 then init
        else if init[m]'(m.2) != (none : Option α) then init
        else
            let mapped_init := init.map (fun x : Option α =>
                match x with
                    | none => 0
                    | some y => y
                )
            init.set m (row[n.1 - 1]'(by omega) - ∑ x : {x : ℕ // x > m.1 ∧ x < n.1}, (row[x]'(x.2.1) * mapped_init[x] ) )
        sorry

/- Read of solution -/
def get_solution (system : linearSystem α k n) (h : system_in_ref kgtn system) (has_sol : ∃ β, beta_is_solution system β) : Vector α (n - 1) := by
    let rows_zipped := system.toArray.zip (Array.finRange k)
    let non_zero_rows := rows_zipped.filter (fun eqn => eqn.1 != 0)
    let last_non_zero_row := non_zero_rows[non_zero_rows.size - 1]?

    let sol_fold_fun : (Vector (α × Bool) (n - 1)) →  ℕ → (Vector (α × Bool) (n - 1)) :=
     sorry



def get_unique_solution (system : linearSystem α k n) (h : system_in_reduced_ref kgtn system)
        : Vector α (n - 1) :=
    have h₁ : ((n.1 - 1) ⊓ ↑k - 0) = ↑n - 1 := by
        apply min_eq_left_of_lt
        refine Nat.lt_trans ?_ kgtn
        omega
    let first_n_minus_one_row := system.extract 0 (n - 1)

    let first_n_minus_one_row_casted : Vector _ (n - 1) :=
        ⟨first_n_minus_one_row.toArray, by rw [Vector.size_toArray]; exact h₁ ⟩
    first_n_minus_one_row_casted.map (fun x : linearEquation α n => x[n.1 - 1]'(by omega))



    /-let rank := get_rank kgtn system h
    let prop : Prop := (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[rank.1] = (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[rank.1 - 1]
    have eq_or_neq: prop ∨ ¬prop := eq_or_ne system[↑rank][↑rank] system[↑rank][↑rank - 1]
    apply Or.elim eq_or_neq
    done-/


end Gaussian
