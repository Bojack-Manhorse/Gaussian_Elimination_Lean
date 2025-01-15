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

variable {α : Type} [Field α] [Inhabited α] {k n : {x : ℕ // x > 1}} (kgeqn : k > n)

/- Assuming `system[i][i] ≠ 0` makes `system[j][i] = 0`: -/
def zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₂ : i ≠ j) (h₃ : (system[i]'(Nat.lt_trans h₀ kgeqn))[i]'(h₀) ≠ 0) : linearSystem α k n := by
    let coef := -((system[j]'(h₁))[i]'(h₀) / (system[i]'(Nat.lt_trans h₀ kgeqn))[i])
    exact add_row system coef i j (Nat.lt_trans h₀ kgeqn) h₁


lemma zero_entry_after_zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : j < k) (h₂ : i ≠ j) (h₃ : (system[i]'(Nat.lt_trans h₀ kgeqn))[i]'(h₀) ≠ 0) : ((zero_entry kgeqn system i j h₀ h₁ h₂ h₃)[j]'(h₁))[i]'(h₀) = 0 := by
    simp [zero_entry]
    rw [zip_index_pick_fst _ _ (by simp) (by simp) i (h₀), zip_index_pick_snd _ _ (by simp) (by simp) i (h₀)]
    simp only [Array.getElem_map]
    rw [vector_to_array_element _ _ h₀, vector_to_array_element _ _ h₀]
    field_simp

/- Maybe make output a dependent pair `⟨system', proof system' has same solution as system⟩`-/
def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) (h₃ : (system[i]'(Nat.lt_trans h₁ kgeqn))[i]'(h₁) ≠ 0) : (linearSystem α k n) := by
    let map_array : Fin k → _ := (fun x => (fun system' : (linearSystem α k n) =>
        zero_entry kgeqn system' i x h₁ (x.2.1) x.2.2 ))
    exact Fin.foldr k map_array system
    sorry

def row_reduce_system (system : linearSystem α k n) : linearSystem α k n := sorry


end Gaussian
