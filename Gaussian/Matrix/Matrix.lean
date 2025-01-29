import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] 

variable {numVars numEqns : ℕ}

/-
  Maybe swap like this?
  Let's see what Julian had in mind.
-/
-- def M₁ : Matrix (Fin 2) (Fin 3) α := !![0, 1, 2; 3, 4, 5]
-- def M₂ : Matrix (Fin 2) (Fin 3) α := !![3, 4, 5; 0, 1, 2]

-- example : Matrix.submatrix (l := Fin 2) (o := Fin 3)
--                            M₁
--                            (fun row ↦ (List.finRange 2)[1 - row])
--                            id = M₂ (α := α) := by
--   ext r c
--   simp [M₁, M₂]
--   fin_cases r <;> fin_cases c <;> rfl

section SystemsOfLinearEquations

/- A pair consisting of a `numEqns × numVars` matrix and a `numEqns × 1` matrix that we wish to find some vector of size `numVars × 1` that's a solution to the pair. -/
structure LinearSystem (numVars numEqns : ℕ) (α : Type) where
  vars : Matrix (Fin numEqns) (Fin numVars) α
  const : Matrix (Fin numEqns) (Fin 1) α

abbrev LinearSystem.kth_const (s : LinearSystem numVars numEqns α) (i : Fin numEqns) : α := s.const i 0

/- Definition of some vector `β` being a solution to some `system : linearSystem`: -/
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

/- A `numEqns × numEqns` matrix `P` such that for any matrix `A`, `P * A` represents swapping rows `i, j` of `A`. -/
def swapRowMatrix (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A `numVars × numVars` `P` such that for any matrix `A`, `A * P` represents swapping columns `i, j` of `A`. -/
def swapColMatrix (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 - (Matrix.stdBasisMatrix i i 1 + Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

end Transvections

section

variable [DecidableEq α]

section DiagonalMatrices

/- Definition of a `numEqns × numVars` matrix being diagonal: -/
def isDiagonal (D : Matrix (Fin numEqns) (Fin numVars) α) : Prop :=
  ∀ i : Fin numEqns, ∀ j : Fin numVars, (i.1 ≠ j.1 → D i j = 0)

instance {D : Matrix (Fin numEqns) (Fin numVars) α} : Decidable (isDiagonal D) := by
  unfold isDiagonal; infer_instance

def parity (x : α) : α := if x = 0 then 0 else 1

lemma parity_of_pos {x : α} (h : x = 0) : parity x = 0 := by simp [parity, h]

lemma parity_of_neg {x : α} (h : x ≠ 0) : parity x = 1 := by simp [parity, h]

def parityCheckFun (system : LinearSystem numVars numEqns α) (i : Fin numEqns) : α × α :=
  if h1 : i < numVars
  then (system.vars i ⟨i.1, by omega⟩, parity (system.const i 1))
  else (0, parity (system.const i 1))

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
def noSolutionDiagonal (system : LinearSystem numVars numEqns α) : Prop :=
  (0, 1) ∈ List.ofFn (parityCheckFun system)

lemma list_ofFn_mem {β : Type} {a : β} {m : ℕ} {i : Fin m} {f : Fin m → β} (aeq : a = f i) : a ∈ List.ofFn f := by
  aesop (add simp List.mem_ofFn)

section ParityCheckFunLemmas

variable {system : LinearSystem numVars numEqns α} {r : Fin numEqns}

lemma parityCheckFun_of_pos (h : r < numVars) :
  parityCheckFun system r = (system.vars r ⟨r.1, by omega⟩, parity (system.const r 0)) := by
  simp [parityCheckFun, *]

lemma parityCheckFun_of_neg (h : ¬r < numVars) :
  parityCheckFun system r = (0, parity (system.const r 0)) := by simp [parityCheckFun, *]

lemma zero_below_diag_no_sol (h₁ : numVars ≤ r) (h₂ : system.const r 0 ≠ 0) : noSolutionDiagonal system := by
  unfold noSolutionDiagonal
  apply list_ofFn_mem (i := r)
  rw [parityCheckFun_of_neg (by omega), parity_of_neg h₂]

lemma not_noSolutionDiagona_iff_isDiagonal_and_zero_one_not_mem_parityCheck :
  ¬noSolutionDiagonal system ↔ (0, 1) ∉ List.ofFn (parityCheckFun system) := by rfl

lemma zero_diag_implies_zero_const (h2 : ¬noSolutionDiagonal system)
                                   (h3 : r < numVars)
                                   (h4 : system.vars r ⟨r.1, by omega⟩ = 0) : (system.const r 0 = 0) := by
  rw [not_noSolutionDiagona_iff_isDiagonal_and_zero_one_not_mem_parityCheck] at h2
  by_contra constneq0
  have parity_zero : parityCheckFun system r = (0, 1) := by
    simp [parityCheckFun_of_pos h3, h4, parity_of_neg constneq0]
  have zero_one_in_list : (0, 1) ∈ List.ofFn (parityCheckFun system) := list_ofFn_mem parity_zero.symm
  contradiction

end ParityCheckFunLemmas

/- Verifies that if `noSolutionDiagonal system h` is true then there are no possible solutions. -/
lemma diagonal_system_has_no_solutions (system : LinearSystem numVars numEqns α) (h : isDiagonal system.vars)
    : noSolutionDiagonal system ↔ ∀ β : Matrix (Fin numVars) (Fin 1) α, ¬ isSol system β := by
  apply Iff.intro
  . sorry
  . sorry

/- Given a system `system` such that `system.vars` is in diagonal form and it has a solution, construct some `β : Matrix (Fin numVars) (Fin 1) α` that should be a solution (i.e. `system.vars * β == system.const`). -/
def getSolDiagonal (system : LinearSystem numVars numEqns α ) : Matrix (Fin numVars) (Fin 1) α :=
  Matrix.of
    fun (i : Fin numVars) (j : Fin 1) =>
      if eqnsgeqvars : numEqns ≤ i
      then (0 : α)
      else
        let i' : Fin numEqns  := ⟨i.1, by omega⟩
        (system.const i' 0) / (system.vars i' i)
    

/- Claimed evaluation of multiplying a diagonal matrix by a vector. -/
def diagMulEval (D : Matrix (Fin numEqns) (Fin numVars) α)
                (β : Matrix (Fin numVars) (Fin 1) α) : Matrix (Fin numEqns) (Fin 1) α :=
    Matrix.of (fun x y =>
    if h : x.1 >= numVars then 0
    else D x ⟨x.1, by omega⟩ * β ⟨x.1, by omega⟩ y)

/- Verification that `diagMulEval` is indeed the actual evaluation. -/
omit [DecidableEq α] in
lemma diag_mul_verify (D : Matrix (Fin numEqns) (Fin numVars) α)
                      (h : isDiagonal D)
                      (β : Matrix (Fin numVars) (Fin 1) α) : D * β = diagMulEval D β := by
  unfold diagMulEval; ext i k
  specialize h i
  rw [Matrix.mul_apply]
  by_cases eq : numVars ≤ i <;> simp [eq]
  · rw [Finset.sum_eq_zero (by specialize h · (by omega); aesop)]
  · rw [Fintype.sum_eq_single]; aesop 

/- Check that the solution from `getSolDiagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (system : LinearSystem numVars numEqns α)
                         (h1 : isDiagonal system.vars) (h2 : ¬ noSolutionDiagonal system)
    : isSol system (getSolDiagonal system) := by
  rw [isSol]
  rw [diag_mul_verify system.vars h1]
  rw [diagMulEval, getSolDiagonal]
  apply Matrix.ext
  intro i k
  simp
  apply Or.elim (le_or_lt numVars ↑i)
  . intro igenvars
    simp only [igenvars, ↓reduceDIte]
    have zero : system.const i k = 0 := by
      by_contra h3
      push_neg at h3
      have h5: noSolutionDiagonal system := by
        apply zero_below_diag_no_sol igenvars
        rwa [Fin.fin_one_eq_zero k] at h3
      exact h2 h5
    rw [zero]
  . intro iltvars
    have h4 : ¬ i ≥ numVars := Nat.not_le_of_lt iltvars
    simp only [h4, ↓reduceDIte]
    have : ¬ numEqns ≤ i := Nat.not_le_of_lt i.2
    simp [Nat.not_le_of_lt i.2]
    apply Or.elim (eq_or_ne (system.vars i ⟨i.1, by omega⟩) 0)
    . intro syseq0
      rw [syseq0]
      ring_nf
      rw [Fin.fin_one_eq_zero k]
      apply Eq.symm
      apply zero_diag_implies_zero_const _ iltvars syseq0
      assumption
    . intro sysneq0
      field_simp
      rw [Fin.fin_one_eq_zero k] at *

end DiagonalMatrices

section ExistenceOfSolutions

lemma left_mul_matrix {m n : ℕ} (C : Matrix (Fin m) (Fin m) α) [Invertible C] (A B : Matrix (Fin m) (Fin n) α) (h : C * A = C * B) : A = B := by
  have h1 : ⅟C * (C * A) = ⅟C * (C * B) := by exact congrArg (HMul.hMul ⅟C) h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc] at h1
  rw [invOf_mul_self] at h1
  simp at h1
  exact h1

lemma left_mul_matrix_iff {m n: ℕ} (C : Matrix (Fin m) (Fin m) α) [Invertible C] (A B : Matrix (Fin m) (Fin n) α) :
    C * A = C * B ↔ A = B := by
  apply Iff.intro
  . intro h
    exact left_mul_matrix C A B h
  . intro h
    exact congrArg (HMul.hMul C) h

def has_solution (system : LinearSystem numVars numEqns α) : Prop :=
  ∃ β : (Matrix (Fin numVars) (Fin 1) α), isSol system β

lemma solutions_preserved_under_transvection (system : LinearSystem numVars numEqns α)
    (P : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P]
    (Q : Matrix (Fin numVars) (Fin numVars) α) [Invertible Q]
    (β : Matrix (Fin numVars) (Fin 1) α)
    : let new_system : LinearSystem numVars numEqns α := ⟨P * system.vars * Q, P * system.const⟩
    isSol system β ↔ isSol new_system (⅟Q * β) := by
  simp [isSol]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ ⅟Q, mul_invOf_self', Matrix.mul_one, Matrix.mul_assoc P _ _]
  apply Iff.symm
  apply left_mul_matrix_iff


end ExistenceOfSolutions

section NonDiagonalSolutions

def get_solution_from_diagonalise (system : LinearSystem numVars numEqns α)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    (h : isDiagonal (P_row * system.vars * P_col))
    /- Need to put something about solutions existing -/
    : Matrix (Fin numVars) (Fin 1) α :=
  let new_system : LinearSystem numVars numEqns α := ⟨P_row * system.vars * P_col, P_row * system.const⟩
  P_col * getSolDiagonal new_system h (sorry)

def check_solution (system : LinearSystem numVars numEqns α)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    (h : let new_system : LinearSystem numVars numEqns α := ⟨P_row * system.vars * P_col, P_row * system.const⟩; isDiagonal new_system.vars)
    : isSol system (get_solution_from_diagonalise system P_row P_col h) := by
  rw [isSol]-- get_solution_from_diagonalise]
  apply left_mul_matrix P_row
  rw [get_solution_from_diagonalise]
  rw [← Matrix.mul_assoc system.vars _ _]
  rw [← Matrix.mul_assoc P_row _ _]
  rw [← Matrix.mul_assoc P_row system.vars _]
  --rw [← new_sys_defn]
  sorry
  --simp only [new_system]
  --apply check_diagonal_sol


end NonDiagonalSolutions

end

end MatrixElimination
