import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] {numVars numEqns : ℕ}

section SystemsOfLinearEquations

/- A pair consisting of a `numEqns × numVars` matrix and a `numEqns × 1` matrix that we wish to find some vector of size `numVars × 1` that's a solution to the pair. -/
structure LinearSystem (numVars numEqns : ℕ) (α : Type) where
  vars : Matrix (Fin numEqns) (Fin numVars) α
  const : Matrix (Fin numEqns) (Fin 1) α

/- Definition of some vector `β` being a solution to some `system : LinearSystem`: -/
def isSol (system : LinearSystem numVars numEqns α) (β : Matrix (Fin numVars) (Fin 1) α) : Prop :=
  system.vars * β = system.const

end SystemsOfLinearEquations

section Transvections

/- From Mathlib Transvection 78-/
def addRowTransvection (c : α) (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + Matrix.stdBasisMatrix i j c

/- From Mathlib Transvection 78-/
def addColTransvection (c : α) (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + Matrix.stdBasisMatrix i j c

/- A `numEqns × numEqns` `P` such that for any matrix `A`, `P * A` represents swapping rows `i, j` of `A`. -/
def swapRowMatrix (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A `numVars × numVars` `P` such that for any matrix `A`, `A * P` represents swapping columns `i, j` of `A`. -/
def swapColMatrix (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

end Transvections

section DiagonalMatrices

-- variable [Inhabited α] [DecidableEq α]

/- Definition of a `numEqns × numVars` being diagonal: -/
def isDiagonal (D : Matrix (Fin numEqns) (Fin numVars) α) : Prop :=
  ∀ i : Fin numEqns, ∀ j : Fin numVars, i.1 ≠ j.1 → D i j = 0

instance {D : Matrix (Fin numEqns) (Fin numVars) α} [DecidableEq α] : Decidable (isDiagonal D) := by
  unfold isDiagonal; infer_instance

def parityCheckFun (system : LinearSystem numVars numEqns α) (i : Fin numEqns) : α × α :=
  if h1 : i < numVars
  then (system.vars i ⟨i.1, by omega⟩, system.const i 1 / system.const i 1)
  else (0, system.const i 1 / system.const i 1)

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
/--
This needs a new name :).
-/
def isFalseDiagonal [DecidableEq α] (system : LinearSystem numVars numEqns α) : Bool :=
  -- So you want to 'run' this - then we don't need to take `h`, we can return `false` instead.
  -- That about correct? ^
  isDiagonal system.vars → (0, 1) ∈ List.ofFn (parityCheckFun system)

lemma list_ofFn_mem {β : Type} {a : β} {m : ℕ} {f : Fin m → β} {i : Fin m}
  (aeq : a = f i) : a ∈ List.ofFn f := by aesop (add simp List.mem_ofFn)

example (m l : ℕ) (φ : Prop) (h : if m < l then False else φ) (h2 : m ≥ l) : φ := by
  have h3 : ¬ m < l := Nat.not_lt.mpr h2
  simp at h
  sorry

section

variable {system : LinearSystem numVars numEqns α} 

lemma parityCheckFun_of_pos {i : Fin numEqns} (h : i < numVars) :
  parityCheckFun system i = (system.vars i ⟨i.1, by omega⟩, system.const i 1 / system.const i 1) := by
  simp [parityCheckFun, h]

lemma parityCheckFun_of_neg {i : Fin numEqns} (h : ¬i < numVars) :
  parityCheckFun system i = (0, system.const i 1 / system.const i 1) := by
  simp [parityCheckFun, h]

variable [DecidableEq α]

lemma not_isFalseDiagional_iff_isDiagonal_and_zero_one_not_mem_parityCheck :
  ¬isFalseDiagonal system ↔ isDiagonal system.vars ∧ (0, 1) ∉ List.ofFn (parityCheckFun system) := by
  simp [isFalseDiagonal]

lemma cond_for_false {i : Fin numEqns}
  (igeq : numVars ≤ i) (cnzero : system.const i 0 ≠ 0) : isFalseDiagonal system := by
  suffices isDiagonal system.vars → (0, 1) ∈ List.ofFn (parityCheckFun system) by aesop (add simp isFalseDiagonal)
  refine λ x ↦ list_ofFn_mem (i := i) ?_
  rw [parityCheckFun_of_neg (by omega)]
  simp; field_simp
  
lemma zero_diag_implies_zero_const {i : Fin numEqns}
  (h2 : ¬isFalseDiagonal system) (h3 : i < numVars) (h4 : system.vars i ⟨i.1, by omega⟩ = 0) :
  (system.const i 0 = 0) := by
  obtain ⟨isDiag, nMem⟩ := not_isFalseDiagional_iff_isDiagonal_and_zero_one_not_mem_parityCheck.1 h2
  by_contra constneq0
  have parity_zero : parityCheckFun system i = (0, 1) := by
    simp [parityCheckFun_of_pos h3, h4]; field_simp
  have zero_one_in_list : (0, 1) ∈ List.ofFn (parityCheckFun system) := list_ofFn_mem parity_zero.symm
  contradiction

/- Verifies that if `isFalseDiagonal system h` is true then there are no possible solutions. -/
lemma diagonal_system_has_no_solutions (system : @LinearSystem α numVars numEqns) (h : isDiagonal system.vars)
    : isFalseDiagonal system h ↔ ∀ β : Matrix (Fin numVars) (Fin 1) α, ¬ isSol system β := by
  apply Iff.intro
  . sorry
  . sorry



/- Given a system `system` such that `system.vars` is in diagonal form and it has a solution, construct some `β : Matrix (Fin numVars) (Fin 1) α` that should be a solution (i.e. `system.vars * β == system.const`). -/
def get_sol_diagonal (system : @LinearSystem α numVars numEqns ) (h1 : isDiagonal system.vars) (h2 : ¬ isFalseDiagonal system h1)
    : Matrix (Fin numVars) (Fin 1) α :=
  Matrix.of
    (fun (i : Fin numVars) (j : Fin 1) =>
      if eqnsgeqvars : i >= numEqns then (0 : α)
      else
        let i' : Fin numEqns  := ⟨i.1, by omega⟩
        (system.const i' 0) / (system.vars i' i)
    )

/- Claimed evaluation of multiplying a diagonal matrix by a vector. -/
def diag_mul_eval (D : Matrix (Fin numEqns) (Fin numVars) α) (h : isDiagonal D) (β : Matrix (Fin numVars) (Fin 1) α) : Matrix (Fin numEqns) (Fin 1) α :=
    Matrix.of (fun x y =>
    if h : x.1 >= numVars then 0
    else D x ⟨x.1, by omega⟩ * β ⟨x.1, by omega⟩ y)

/- Verification that `diag_mul_eval` is indeed the actual evaluation. -/
lemma diag_mul_verify (D : Matrix (Fin numEqns) (Fin numVars) α) (h : isDiagonal D) (β : Matrix (Fin numVars) (Fin 1) α)
    : D * β = diag_mul_eval D h β := by
  rw [diag_mul_eval]
  apply Matrix.ext
  intro i k
  rw [Matrix.mul_apply]
  apply Or.elim (le_or_lt numVars ↑i)
  . intro igenvars
    have all_zero : ∀ j : Fin (numVars), D i j * β j k = 0 := by
      intro j
      have D_zero := h i j (by omega)
      simp only [D_zero, zero_mul]
    rw [Fintype.sum_eq_zero _ all_zero]
    simp only [ge_iff_le, Matrix.of_apply, igenvars]
    rfl
  . intro ilenvars
    have inegvars : ¬ numVars ≤ i := Nat.not_le_of_lt ilenvars
    have all_zero : ∀ j : Fin numVars, j.1 ≠ i.1 → D i j * β j k = 0 := by
      intro j ineqj
      have D_zero := h i j (id (Ne.symm ineqj))
      simp only [D_zero, zero_mul]
    rw [Fintype.sum_eq_single ⟨i, ilenvars⟩ (fun x neq => all_zero x (Fin.val_ne_of_ne neq))]
    simp only [ge_iff_le, Matrix.of_apply, inegvars, ↓reduceDIte]

/- Check that the solution from `get_sol_diagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (system : @LinearSystem α numVars numEqns ) (h1 : isDiagonal system.vars) (h2 : ¬ isFalseDiagonal system h1)
    : isSol system (get_sol_diagonal system h1 h2) := by
  rw [isSol, beq_iff_eq]
  --rw [isDiagonal] at h1
  simp at h2
  rw [diag_mul_verify system.vars h1]
  rw [diag_mul_eval, get_sol_diagonal]
  apply Matrix.ext
  intro i k
  --
  simp
  apply Or.elim (le_or_lt numVars ↑i)
  . intro igenvars
    simp only [igenvars, ↓reduceDIte]
    have zero : system.const i k = 0 := by
      by_contra h3
      push_neg at h3
      have h5: isFalseDiagonal system h1 := by
        apply cond_for_false h1 i
        rw [Fin.fin_one_eq_zero k] at h3
        exact ⟨igenvars, h3⟩
      sorry --exact h5 h2
    rw [zero]
  . intro iltvars
    have h4 : ¬ i ≥ numVars := Nat.not_le_of_lt iltvars
    simp only [h4, ↓reduceDIte]
    have : ¬ numEqns ≤ i := Nat.not_le_of_lt i.2
    simp [Nat.not_le_of_lt i.2]
    apply Or.elim (eq_or_ne (system.vars i ⟨i.1, by omega⟩) 0)
    . intro syseq0
      rw [syseq0]
      ring
      rw [Fin.fin_one_eq_zero k]
      apply Eq.symm
      apply zero_diag_implies_zero_const h1 _ i iltvars syseq0
      assumption
    . intro sysneq0
      field_simp
      rw [Fin.fin_one_eq_zero k] at *

end

end DiagonalMatrices


end MatrixElimination
