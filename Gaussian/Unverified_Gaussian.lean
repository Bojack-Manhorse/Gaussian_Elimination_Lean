import Gaussian.Row_Operations


namespace unverified

open RowOperations

variable {α : Type} [Field α] [DecidableEq α] [Inhabited α] {k n : {x : ℕ // x > 1}} (kgtn : k > n)

/- Assuming `system[i][i] ≠ 0` makes `system[j][i] = 0` by row operations.-/
def zero_entry (system : linearSystem α k n) (i j : ℕ ) (h₀ : i < n) (h₁ : j < k) : linearSystem α k n :=
    let coef := -(system[j][i] / (system[i]'(Nat.lt_trans h₀ kgtn))[i])
    add_row system coef i j (Nat.lt_trans h₀ kgtn) h₁

/- Makes the entry at `system[i][i]` non-zero -/
def ensure_non_zero_at_i (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : linearSystem α k n :=
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

/- A function we fold over to zero out an entire column-/
def fold_func_i (i : ℕ) (h₁ : i < n) := fun (system : (linearSystem α k n)) (x : Fin i) => zero_entry kgtn system i x h₁ (Nat.lt_trans x.2 (Nat.lt_trans h₁ kgtn))

/- Zero out all the elements directly above `system[i][i]`. -/
def pivot_system_above (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) :=
    Fin.foldl i (fold_func_i kgtn i h₁) system

/- Zero out all the elemnts directly below `system[i][i]`. -/
def pivot_system_below (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) :=
    have h₉ : i < k := Nat.lt_trans h₁ kgtn
    have h₈ (x : Fin (k - i - 1)) : x.1 + ↑i + 1 < ↑k := by
        rw [add_assoc]
        apply Nat.add_lt_of_lt_sub
        exact x.isLt
    Fin.foldr (k - i - 1) (fun (x : Fin (k - i - 1)) (system' : (linearSystem α k n)) => zero_entry kgtn system' i (x + i + 1) h₁ (h₈ x) ) system

def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < n) : (linearSystem α k n) :=
  /-
  by
  apply pivot_system_above kgtn _ i h₁
  apply pivot_system_below kgtn _ i h₁
  apply ensure_non_zero_at_i kgtn _ i h₁
  exact system
  -/
  pivot_system_above kgtn (pivot_system_below kgtn (ensure_non_zero_at_i kgtn system i h₁) i h₁) i h₁

def row_reduce_system (system : linearSystem α k n) : linearSystem α k n :=
    Fin.foldr n (fun (column : Fin n) (system' : (linearSystem α k n)) => pivot_system kgtn system' column.1 column.2) system


end unverified
