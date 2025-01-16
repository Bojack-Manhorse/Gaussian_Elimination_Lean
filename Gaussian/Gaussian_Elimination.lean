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

variable {α : Type} [Field α] [Inhabited α] {k n : {x : ℕ // x > 1}} (kgtn : k > n)


/- Assuming `system[i][i] ≠ 0` makes `system[j][i] = 0`: -/
def zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) : linearSystem α k n := by
    let coef := -((system[j]'(h₁))[i]'(h₀) / (system[i]'(Nat.lt_trans h₀ kgtn))[i])
    exact add_row system coef i j (Nat.lt_trans h₀ kgtn) h₁


lemma zero_entry_after_zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₃ : (system[i]'(Nat.lt_trans h₀ kgtn))[i]'(h₀) ≠ 0) : ((zero_entry kgtn system i j h₀ h₁)[j]'(h₁))[i]'(h₀) = 0 := by
    simp [zero_entry]
    rw [zip_index_pick_fst _ _ (by simp) (by simp) i (h₀), zip_index_pick_snd _ _ (by simp) (by simp) i (h₀)]
    simp only [Array.getElem_map]
    rw [vector_to_array_element _ _ h₀, vector_to_array_element _ _ h₀]
    field_simp

structure system_non_zero_i_pair (i : ℕ) (h₀ : i < n) where
    system : linearSystem α k n
    non_zero_i : (system[i]'(Nat.lt_trans h₀ kgtn))[i]'(h₀) ≠ 0

def zero_entry_pair (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₂ : i ≠ j) (system_pair : system_non_zero_i_pair kgtn i h₀) : (system_non_zero_i_pair kgtn i h₀) :=
    sorry


def pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    exact Fin.foldr i (fun (x : Fin i) (system' : (linearSystem α k n)) => zero_entry kgtn system' i x h₁ (Nat.lt_trans x.2 h₉) ) system

def pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := by
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    have h₈ (x : Fin (k - i - 1)) : x.1 + ↑i + 1 < ↑k := by
        rw [add_assoc]
        apply Nat.add_lt_of_lt_sub
        exact x.isLt
    exact Fin.foldr (k - i - 1) (fun (x : Fin (k - i - 1)) (system' : (linearSystem α k n)) => zero_entry kgtn system' i (x + i + 1) h₁ (h₈ x) ) system

def ensure_non_zero_at_i (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : linearSystem α k n :=
    let i_th_column_array := Array.map (fun lin_eqn => lin_eqn[i]'(h₁)) system.toArray
    let non_zero := Array.filter (fun x => ) i_th_column_array
    sorry


/- Maybe make output a dependent pair `⟨system', proof system' has same solution as system⟩`-/
def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) := pivot_system_above kgtn (pivot_system_below kgtn system i h₁) i h₁

def row_reduce_system (system : linearSystem α k n) : linearSystem α k n := Fin.foldr n (fun (column : Fin n) (system' : (linearSystem α k n)) => pivot_system kgtn system' column.1 column.2) system

end Gaussian
