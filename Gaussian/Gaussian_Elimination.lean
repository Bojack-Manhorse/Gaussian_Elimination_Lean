import Gaussian.Row_Operations

namespace Gaussian

open LinearEquation

open RowOperations

variable {α : Type} [Field α] [Inhabited α] {k n : {x : ℕ // x > 1}}

def zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : i < k) (h₂ : j < k) : linearSystem α k n := by
    let coef := -(system[j].coefficients[i]'(by rw [linear_equation.length]; exact h₀) / (system[i]'(h₁)).coefficients[i]'(by rw [linear_equation.length]; exact h₀))
    exact add_row system coef i j h₁ h₂

lemma zero_entry_after_zero_entry (system : linearSystem α k n) (i j : ℕ) (h₀ : i < n) (h₁ : i < k) (h₂ : j < k) (h₃ : i ≠ j) (h₄ : ) : (zero_entry system i j h₀ h₁ h₂)[j].coefficients[i]'(by rw [linear_equation.length]; exact h₀) = 0 := by



def pivot_system (system : linearSystem α k n) (i : ℕ) (h₁ : i < k) : (linearSystem α k n) := sorry




def row_reduce_system (system : linearSystem α k n) : linearSystem α k n := sorry


end Gaussian
