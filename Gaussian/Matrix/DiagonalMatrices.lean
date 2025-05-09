import Gaussian.Matrix.Transvections
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

variable {numVars numEqns : ℕ}


section DiagonalMatrices

/- Definition of a `numEqns × numVars` matrix being diagonal: -/
def isDiagonal (D : Matrix (Fin numEqns) (Fin numVars) α) : Prop :=
  ∀ i : Fin numEqns, ∀ j : Fin numVars, (i.1 ≠ j.1 → D i j = 0)

instance {D : Matrix (Fin numEqns) (Fin numVars) α} [DecidableEq α] : Decidable (isDiagonal D) := by
  unfold isDiagonal; infer_instance

def constIndicator (x : α) : α := if x = 0 then 0 else 1

lemma parity_of_pos {x : α} (h : x = 0) : constIndicator x = 0 := by simp [constIndicator, h]

lemma parity_of_neg {x : α} (h : x ≠ 0) : constIndicator x = 1 := by simp [constIndicator, h]

def parityCheckFun (system : LinearSystem numVars numEqns α) (i : Fin numEqns) : α × α :=
  if h1 : i < numVars
  then (system.vars i ⟨i.1, by omega⟩, constIndicator (system.const i 0))
  else (0, constIndicator (system.const i 0))

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
def noSolutionDiagonal (system : LinearSystem numVars numEqns α) : Prop :=
  (0, 1) ∈ Set.range (parityCheckFun system)

/--
Of course this holds.
-/
example {system : LinearSystem numVars numEqns α} :
  noSolutionDiagonal system ↔ (0, 1) ∈ List.ofFn (parityCheckFun system) :=
  (List.mem_ofFn _ _).symm

instance {system : LinearSystem numVars numEqns α} : Decidable (noSolutionDiagonal system) := by
  unfold noSolutionDiagonal
  infer_instance

lemma list_ofFn_mem {β : Type} {a : β} {m : ℕ} {i : Fin m} {f : Fin m → β} (aeq : a = f i) : a ∈ List.ofFn f := by
  aesop (add simp List.mem_ofFn)

section ParityCheckFunLemmas

variable {system : LinearSystem numVars numEqns α} {r : Fin numEqns}

lemma parityCheckFun_of_pos (h : r < numVars) :
  parityCheckFun system r = (system.vars r ⟨r.1, by omega⟩, constIndicator (system.const r 0)) := by
  simp [parityCheckFun, *]

lemma parityCheckFun_of_neg (h : ¬r < numVars) :
  parityCheckFun system r = (0, constIndicator (system.const r 0)) := by simp [parityCheckFun, *]

lemma zero_below_diag_no_sol (h₁ : numVars ≤ r) (h₂ : system.const r 0 ≠ 0) : noSolutionDiagonal system := by
  refine' Set.mem_range.2 ⟨r, _⟩
  rw [parityCheckFun_of_neg (by omega), parity_of_neg h₂]

lemma not_noSolutionDiagona_iff_isDiagonal_and_zero_one_not_mem_parityCheck :
  ¬noSolutionDiagonal system ↔ (0, 1) ∉ Set.range (parityCheckFun system) := by rfl

lemma zero_diag_implies_zero_const (h2 : ¬noSolutionDiagonal system)
                                   (h3 : r < numVars)
                                   (h4 : system.vars r ⟨r.1, by omega⟩ = 0) : (system.const r 0 = 0) := by
  rw [not_noSolutionDiagona_iff_isDiagonal_and_zero_one_not_mem_parityCheck] at h2
  by_contra constneq0
  have parity_zero : parityCheckFun system r = (0, 1) := by
    simp [parityCheckFun_of_pos h3, h4, parity_of_neg constneq0]
  aesop

end ParityCheckFunLemmas

lemma list_ofFn_exits {β : Type} {list : List β} {a : β} (h : a ∈ list) : ∃ b : Fin (list.length), a = list[b] := by
  obtain ⟨n, hn⟩ := List.get_of_mem h
  use n
  exact (Eq.symm hn)

example (a b : ℕ) (n : Fin a) (h : a = b) : (Fin.cast h n).1 = n.1 := rfl

variable {system : LinearSystem numVars numEqns α}

/- Given a system `system` such that `system.vars` is in diagonal form and it has a solution, construct some `β : Matrix (Fin numVars) (Fin 1) α` that should be a solution (i.e. `system.vars * β == system.const`). -/
def getSolDiagonal (system : LinearSystem numVars numEqns α ) : Matrix (Fin numVars) (Fin 1) α :=
  Matrix.of
    fun (i : Fin numVars) (j : Fin 1) =>
      if eqnsgeqvars : numEqns ≤ i
      then 0
      else let i' : Fin numEqns := ⟨i.1, by omega⟩
           system.const i' 0 / system.vars i' i

/- Claimed evaluation of multiplying a diagonal matrix by a vector. -/
def diagMulEval (D : Matrix (Fin numEqns) (Fin numVars) α) (β : Matrix (Fin numVars) (Fin 1) α) : Matrix (Fin numEqns) (Fin 1) α :=
    Matrix.of fun x y =>
      if h : numVars ≤ x.1
      then 0
      else D x ⟨x.1, by omega⟩ * β ⟨x.1, by omega⟩ y

/- Verification that `diagMulEval` is indeed the actual evaluation. -/
omit [DecidableEq α] in
lemma diagMul_verify {D : Matrix (Fin numEqns) (Fin numVars) α}
                     {β : Matrix (Fin numVars) (Fin 1) α}
                     (h : isDiagonal D) : D * β = diagMulEval D β := by
  unfold diagMulEval; ext i k
  specialize h i
  rw [Matrix.mul_apply]
  by_cases eq : numVars ≤ i <;> simp [eq]
  · rw [Finset.sum_eq_zero (by specialize h · (by omega); aesop)]
  · rw [Fintype.sum_eq_single]; aesop

/- Check that the solution from `getSolDiagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (h1 : isDiagonal system.vars)
                         (h2 : ¬ noSolutionDiagonal system) : isSol system (getSolDiagonal system) := by
  unfold isSol
  rw [diagMul_verify h1]
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
      ring
      rw [Fin.fin_one_eq_zero k]
      apply Eq.symm
      apply zero_diag_implies_zero_const _ iltvars syseq0
      assumption
    . intro sysneq0
      field_simp
      rw [Fin.fin_one_eq_zero k] at *

/- Verifies that if `noSolutionDiagonal system h` is true then there are no possible solutions. -/
lemma diagonal_system_has_no_solutions (h : isDiagonal system.vars)
    : noSolutionDiagonal system → ¬ hasSolution system := by
  . intro no_sol
    intro has_sol
    rw [noSolutionDiagonal] at no_sol
    simp [list_ofFn_exits] at no_sol
    obtain ⟨n, hn⟩ := no_sol
    obtain ⟨β, sol⟩ := has_sol
    simp [isSol] at sol
    simp [parityCheckFun] at hn
    aesop
    . aesop (add simp constIndicator) --(add simp diagMul_verify)
      have diagmul : (system.vars * β) = diagMulEval system.vars β := diagMul_verify h
      have : (system.vars * β) n 0 = 0 := by
        rw [diagMul_verify]
        simp [diagMulEval]
        intro h
        aesop
        exact h
      aesop
    . aesop (add simp constIndicator)
      have diagmul : (system.vars * β) = diagMulEval system.vars β := diagMul_verify h
      have : (system.vars * β) n 0 = 0 := by
        rw [diagmul, diagMulEval]
        simp only [Matrix.of_apply, h_1, ↓reduceDIte]
      aesop

end DiagonalMatrices
