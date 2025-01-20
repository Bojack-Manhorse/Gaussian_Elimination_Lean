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

variable {α : Type} [Field α] [DecidableEq α] [Inhabited α] {k n : {x : ℕ // x > 1}} (i j : ℕ) (h₁ : i < n) (h₂ : j < k) (kgtn : k > n)

def iltk (i : ℕ) (h : i < n.1) : i < k := Nat.lt_trans h kgtn


/- Assuming `system[i][i] ≠ 0` makes `system[j][i] = 0`: -/
def zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) : linearSystem α k n := by
    let coef := -((system[j]'(h₁))[i]'(h₀) / (system[i]'(Nat.lt_trans h₀ kgtn))[i])
    exact add_row system coef i j (Nat.lt_trans h₀ kgtn) h₁


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

def pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    exact Fin.foldr i (fun (x : Fin i) (system' : (linearSystem α k n)) => zero_entry kgtn system' i x h₁ (Nat.lt_trans x.2 h₉) ) system

lemma zero_above_pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (system[i]'(Nat.lt_trans h₁ kgtn))[i] ≠ 0 → ∀ eqn : Fin i, ((pivot_system_above kgtn system i h₁)[eqn]'(Nat.lt_trans (Nat.lt_trans eqn.2 h₁) kgtn))[i]'(h₁) = 0 := by
    intro sysneq0
    intro eqn
    rw [pivot_system_above]
    /- How to induct on this?! -/


def pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    have h₈ (x : Fin (k - i - 1)) : x.1 + ↑i + 1 < ↑k := by
        rw [add_assoc]
        apply Nat.add_lt_of_lt_sub
        exact x.isLt
    exact Fin.foldr (k - i - 1) (fun (x : Fin (k - i - 1)) (system' : (linearSystem α k n)) => zero_entry kgtn system' i (x + i + 1) h₁ (h₈ x) ) system

lemma zero_below_pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n)
        : (system[i]'(Nat.lt_trans h₁ kgtn))[i] ≠ 0 → ∀ eqn : Fin (k - i - 1), ((pivot_system_below kgtn system i h₁)[eqn + i - 1])[i]'(h₁) = 0 := sorry

/- Makes the entry at `system[i][i]` non-zero -/
def ensure_non_zero_at_i (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : linearSystem α k n :=
    /- Only look below the `i-th` column when looking for non-zero element -/
    let entire_i_th_column : Array α := system.toArray.map (fun lin_eqn => lin_eqn[i]'(h₁))
    let entire_i_th_column_zipped : _ := entire_i_th_column.zipWithIndex
    let i_th_column_below_zipped : Array (α × ℕ) := entire_i_th_column_zipped.extract i (k + 1)

    let non_zero := Array.filter (fun x => x.1 != 0) i_th_column_below_zipped
    if non_zero.size > 0 then
        /- Question: How to pick first non-zero element of `i_th_column_array`?-/
        let index : ℕ := (non_zero[0]!).2
        have indltk : index < ↑k := sorry
        by refine swap_row system i index (Nat.lt_trans h₁ kgtn) indltk
    else
        by exact system


def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    apply pivot_system_above kgtn _ i h₁
    apply pivot_system_below kgtn _ i h₁
    apply ensure_non_zero_at_i kgtn _ i h₁
    exact system

def row_reduce_system (system : linearSystem α k n) : linearSystem α k n :=
    Fin.foldr n (fun (column : Fin n) (system' : (linearSystem α k n)) => pivot_system kgtn system' column.1 column.2) system

def system_in_upper_triangular (system : linearSystem α k n) : Prop :=
    ∀ (var : Fin n) (eqn : Fin k), ( eqn.1 > var.1 → ((row_reduce_system kgtn system)[eqn]'(eqn.2))[var]'(var.2) = 0)

lemma upper_triangular_after_row_reduce (system : linearSystem α k n)
        : system_in_upper_triangular kgtn (row_reduce_system kgtn system) := by
    sorry

def system_in_ref (system : linearSystem α k n) : Prop := (system_in_upper_triangular kgtn system) ∧ (∀ i : Fin n, (system[i]'(Nat.lt_trans i.2 kgtn))[i] ≠ 0 → ∀ j : Fin k, system[j][i] = 0)

/- Need this to be a sigma type of ⟨rank, rank < n, ∀ x > rank, system[x] = 0 ⟩ -/
def get_rank (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) : {x : ℕ // x < n} :=
    sorry

/- Rank row is non-zero -/
lemma non_zero_at_rank (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) : system[(get_rank kgtn system h).1]'(Nat.lt_trans (get_rank kgtn system h).2 kgtn) ≠ 0 := sorry

/- Last row has atleast two non-zero entries, if last entry is non-zero-/
lemma last_row_proper_form (system : linearSystem α k n) (h : system_in_upper_triangular kgtn system) (has_sol : ∃ β, beta_is_solution system β) :
        let rank := get_rank kgtn system h
        (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[↑n - 1] = 0 → ∃ index : Fin (n - 1), (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[index] ≠ 0 := sorry



/- Read of solution -/
def get_solution (system : linearSystem α k n) (h : system_in_ref kgtn system) (has_sol : ∃ β, beta_is_solution system β) : Vector α (n - 1) := by

    /-let rank := get_rank kgtn system h
    let prop : Prop := (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[rank.1] = (system[rank.1]'(Nat.lt_trans rank.2 kgtn))[rank.1 - 1]
    have eq_or_neq: prop ∨ ¬prop := eq_or_ne system[↑rank][↑rank] system[↑rank][↑rank - 1]
    apply Or.elim eq_or_neq
    done-/





end Gaussian
