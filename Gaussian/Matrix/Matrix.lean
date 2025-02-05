import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic.FieldSimp

--set_option maxHeartbeats 1000000

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

abbrev LinearSystem.const' (system : LinearSystem numVars numEqns α) (d : Fin numEqns) : α := system.const d 0

/- Definition of some vector `β` being a solution to some `system : linearSystem`: -/
def isSol (system : LinearSystem numVars numEqns α) (β : Matrix (Fin numVars) (Fin 1) α) : Prop :=
  system.vars * β = system.const

def hasSolution (system : LinearSystem numVars numEqns α) : Prop :=
  ∃ β : (Matrix (Fin numVars) (Fin 1) α), isSol system β

end SystemsOfLinearEquations

section Transvections

/- Set `(c : α)` implicit? -/
/- Put c not zero as assumption in subseuent lemmas rather than in lemma-/
/- Try not to require proofs in the assumptions of definitions-/
/- From Mathlib Transvection 78-/
def addRowTransvection (c : α) (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α  :=
  1 + Matrix.stdBasisMatrix i j c

/- From Mathlib Transvection 78-/
def addColTransvection (c : α) (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + Matrix.stdBasisMatrix i j c

/- Do row₁ row₂ maybe?-/
/- A `numEqns × numEqns` matrix `P` such that for any matrix `A`, `P * A` represents swapping rows `i, j` of `A`. -/
def swapRowMatrix (i j : Fin numEqns) : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + ( -Matrix.stdBasisMatrix i i 1 + -Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A `numVars × numVars` `P` such that for any matrix `A`, `A * P` represents swapping columns `i, j` of `A`. -/
def swapColMatrix' (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (- Matrix.stdBasisMatrix i i 1 + - Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

def swapColMatrix (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (- Matrix.stdBasisMatrix i i 1 + - Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

/- A type saying that a matrix is of the form in `addRowTransvection`. -/
abbrev addRowType :=
  {x : Matrix (Fin numEqns) (Fin numEqns) α // ∃ coef : α, ∃ i j : Fin numEqns, i ≠ j ∧ x = addRowTransvection coef i j}

/- A type saying that a matrix is of the form in `addColTransvection`. -/
abbrev addColType :=
  {x : Matrix (Fin numVars) (Fin numVars) α // ∃ coef : α, ∃ i j : Fin numVars, i ≠ j ∧ x = addColTransvection coef i j}

end Transvections

section TransvectionLemmas

/- Lemma that describes `addRowTransvection` in terms of `Matrix.of`. -/
lemma addRowTransvection_lemma (c : α) (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (addRowTransvection c i j) * M =
      Matrix.of (fun x y =>
        if x = i then M i y + c * M j y
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp [addRowTransvection, Matrix.add_mul]
  aesop (add simp Matrix.StdBasisMatrix.mul_left_apply_same)

/- Lemma that describes `addColTransvection` in terms of `Matrix.of`. -/
lemma addColTransvection_lemma (c : α) (i j : Fin numVars) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : M * (addColTransvection c i j) =
      Matrix.of (fun x y =>
        if y = j then M x j + c * M x i
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp only [addColTransvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.of_apply]
  aesop (add simp mul_comm) (add simp Matrix.StdBasisMatrix.mul_right_apply_same)

/- Lemma that describes `swapRowMatrix` in terms of `Matrix.of`. -/
lemma swapRowMatrix_lemma (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (swapRowMatrix i j) * M =
      Matrix.of (fun x y =>
        if x = i then M j y
        else if x = j then M i y
        else M x y) := by
  apply Matrix.ext
  intro row col
  simp only [swapRowMatrix, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.add_apply, Matrix.neg_apply]
  apply Or.elim (eq_or_ne row i)
  . intro roweqi
    simp only [roweqi, ↓reduceIte]
    apply Or.elim (eq_or_ne i j)
    . intro ieqj
      simp only [ieqj, Matrix.StdBasisMatrix.mul_left_apply_same, one_mul,
        add_neg_cancel_comm_assoc, neg_add_cancel_left, Matrix.of_apply, ↓reduceIte]
    . intro ineqj
      simp only [Matrix.StdBasisMatrix.mul_left_apply_same, one_mul, ne_eq, ineqj,
        not_false_eq_true, Matrix.StdBasisMatrix.mul_left_apply_of_ne, neg_zero, add_zero,
        add_neg_cancel, zero_add, Matrix.of_apply, ↓reduceIte]
  . aesop

/- Lemma that describes `swapColMatrix` in terms of `Matrix.of`. -/
lemma swapColMatrix_lemma (i j : Fin numVars) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : M * (swapColMatrix i j) =
      Matrix.of (fun x y =>
        if y = i then M x j
        else if y = j then M x i
        else M x y ) := by
  apply Matrix.ext
  intro row col
  simp only [swapColMatrix, Matrix.mul_add, Matrix.mul_one, Matrix.mul_neg, Matrix.add_apply, Matrix.neg_apply, Matrix.of_apply]
  apply Or.elim (eq_or_ne col i)
  . intro coleqi
    simp only [coleqi, Matrix.StdBasisMatrix.mul_right_apply_same, mul_one, add_neg_cancel_left,
      ↓reduceIte]
    apply Or.elim (eq_or_ne i j)
    . intro ieqj
      simp only [ieqj, Matrix.StdBasisMatrix.mul_right_apply_same, mul_one, neg_add_cancel_left]
    . intro ineqj
      simp [ineqj]
  . aesop

end TransvectionLemmas

section

variable [DecidableEq α]

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

/- After transforming a system by matrices `P` and `Q`, gives a way to go between solutions of the two systems. -/
lemma solutions_preserved_under_transvection (system : LinearSystem numVars numEqns α)
    (P : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P]
    (Q : Matrix (Fin numVars) (Fin numVars) α) [Invertible Q]
    (β : Matrix (Fin numVars) (Fin 1) α)
    : isSol system β ↔ isSol ⟨P * system.vars * Q, P * system.const⟩ (⅟Q * β) := by
  simp [isSol]
  rw [← Matrix.mul_assoc, Matrix.mul_assoc _ _ ⅟Q, mul_invOf_self', Matrix.mul_one, Matrix.mul_assoc P _ _]
  apply Iff.symm
  apply left_mul_matrix_iff

end ExistenceOfSolutions

section NonDiagonalSolutions

/- Gives a solution to system via diagonalising `system.vars` to `new_system` and finding using `getSolDiagonal` on the `new_system`. -/
def get_solution_from_diagonalise (system : LinearSystem numVars numEqns α)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    : Matrix (Fin numVars) (Fin 1) α :=
  let new_system : LinearSystem numVars numEqns α := ⟨P_row * system.vars * P_col, P_row * system.const⟩
  P_col * getSolDiagonal new_system

/- Verifies the above solution is correct. -/
lemma check_solution (system : LinearSystem numVars numEqns α)
    (system_has_sol : hasSolution system)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    (h : isDiagonal (P_row * system.vars * P_col))
    : isSol system (get_solution_from_diagonalise system P_row P_col) := by
  rw [isSol]
  apply left_mul_matrix P_row
  rw [get_solution_from_diagonalise]
  rw [← Matrix.mul_assoc system.vars _ _]
  rw [← Matrix.mul_assoc P_row _ _]
  rw [← Matrix.mul_assoc P_row system.vars _]
  set ls₁ := P_row * system.vars * P_col with eq
  set ls₂ := P_row * system.const with eq₂
  set ls₃ : LinearSystem numVars numEqns α := ⟨ls₁, ls₂⟩ with eq₃
  rw [show ls₁ = ls₃.vars by rfl, show ls₂ = ls₃.const by rfl]
  rw [← isSol]
  apply check_diagonal_sol
  assumption
  obtain ⟨β, hb⟩ := system_has_sol
  rw [isSol] at hb
  have sol_to_ls₃: ls₃.vars * (⅟P_col * β) = ls₃.const := by
    rw [← show ls₁ = ls₃.vars by rfl, eq, ← show ls₂ = ls₃.const by rfl, eq₂ ]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc _ _ β, mul_invOf_self', Matrix.one_mul, Matrix.mul_assoc, hb]
  have exists_sol_to_ls₃ : hasSolution ls₃ := ⟨⅟P_col * β, sol_to_ls₃⟩
  aesop (add simp diagonal_system_has_no_solutions)

end NonDiagonalSolutions

section Diagonalise

section PivotFunctions

def zeroOutColMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + -(Matrix.stdBasisMatrix row_index row_index 1)
    + -∑ (row : Fin numEqns), Matrix.stdBasisMatrix row row_index (M row ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)

def zeroOutRowMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : Matrix (Fin numVars) (Fin numVars) α :=
  1 + -(Matrix.stdBasisMatrix col_index col_index 1)
    + -∑ (col : Fin numVars), Matrix.stdBasisMatrix col col_index (M ⟨col_index.1, by omega⟩ col / M ⟨col_index, by omega⟩ col_index)

lemma zeroOutColMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    --(non_zero : M row_index ⟨row_index.1, by omega⟩ ≠ 0)
    : (zeroOutColMatrix' M row_index rowltvar) * M =
        Matrix.of (fun x y =>
          if x = row_index ∧ y.1 ≠ row_index.1 then M x y - ((M row_index y) * (M x y / M row_index y))
          else M x y) := by
  rw [zeroOutColMatrix']
  simp only [Matrix.add_mul, Matrix.one_mul, Matrix.neg_mul, ne_eq]
  apply Matrix.ext
  intro row col
  simp [Matrix.of_apply]
  by_cases h : (row = row_index ∧ ¬col.1 = row_index.1)
  . simp [h]
    sorry
    --rw [Matrix.mul_apply]
  . simp [h]
    sorry

lemma zeroOutRowMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    --(non_zero : M ⟨col_index.1, by omega⟩ col_index ≠ 0)
    : (M * zeroOutRowMatrix' M col_index collteqn) =
        Matrix.of (fun x y =>
          if y = col_index ∧ x.1 ≠ col_index.1 then M x y - ((M x col_index) * (M x y / M x col_index))
          else M x y) := by
  sorry

/- Two lemmas to show that the identity is technically a row and column transvection. -/
lemma id_is_row_transvection
    (eqngtone : 1 < numEqns)
    : 1 = addRowTransvection (0 : α) ⟨0, by omega⟩ ⟨1, eqngtone⟩ := by
  simp [addRowTransvection]

lemma id_is_col_transvection
    (vargtone : 1 < numVars)
    : 1 = addColTransvection (0 : α) ⟨0, by omega⟩ ⟨1, vargtone⟩ := by
  simp [addColTransvection]

/- Given a matrix `M`, makes the entry at `M index index` non-zero by trying column then row swaps-/
def makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : (Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numVars) (Fin numVars) α) :=
  if h1 : index ≥ numEqns then (1, 1)
  else if h2 : M ⟨index.1, by omega⟩ index ≠ 0 then (1, 1)
  else
    let column := List.ofFn
      (fun x : Fin numEqns =>
        (M x index, x))
    let column_filtered := column.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
    if geq : column_filtered.length > 0
      then (swapRowMatrix (column_filtered[0]'(geq)).2 ⟨index.1, Nat.gt_of_not_le h1⟩, 1)
    else
      let index' : Fin numEqns := ⟨index.1, by omega⟩
      let row := List.ofFn (fun x : Fin numVars => (M index' x, x))
      let row_filtered := row.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
      if geq : row_filtered.length > 0
        then (1, swapColMatrix (row_filtered[0]'(geq)).2 index)
      else (1, 1)

/- Zeroes out the entire row and column at `index` except for `M index index`. -/
def pivotAtIndex
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  if h : numEqns ≤ index.1 then
    swapped
  else
    (zeroOutColMatrix' swapped ⟨index.1, by omega⟩ (index.2)) * swapped * (zeroOutRowMatrix' swapped index (by omega))

/- Asserts that a matrix `M : Matrix (Fin numEqns) (Fin numVars) α` is diagonal outside the submatrix of indices greater than `index`. -/
def diagonalOutsideInnerBlock (M : Matrix (Fin numEqns) (Fin numVars) α) (index : Fin numVars)
    : Prop :=
  ∀ row : Fin numEqns, ∀ col : Fin numVars, (row.1 < index.1 ∨ col.1 < index.1) → row.1 ≠ col.1 → M row col = 0

#check Matrix.submatrix

end PivotFunctions

section SwapLemmas

lemma same_swap_identity_1 (i : Fin numEqns) : swapRowMatrix i i = (1 : Matrix (Fin numEqns) (Fin numEqns) α) := by
  ext row col
  simp [swapRowMatrix, Matrix.stdBasisMatrix]
  aesop

lemma same_swap_identity_2 (i : Fin numVars) : swapColMatrix i i = (1 : Matrix (Fin numVars) (Fin numVars) α) := by
  ext row col
  simp [swapColMatrix, Matrix.stdBasisMatrix]
  aesop

/- The next two lemmas assert that the result from applying `makeNonZeroAtDiag` will always be a swap row/column matrix. -/

lemma only_swaps_or_indentity_from_makeNonZeroAtDiag_right
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : (∃ i j : Fin numEqns, (makeNonZeroAtDiag M index).1 = swapRowMatrix i j ∧ (index.1 ≤ i.1 ∧ index.1 ≤ j.1)) ∨ (makeNonZeroAtDiag M index).1 = 1 := by
  rw [makeNonZeroAtDiag]
  by_cases indeqns : numEqns ≤ index
  . simp [indeqns]
  . simp [indeqns]
    set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
    by_cases M_zero : M ⟨↑index, by omega⟩ index = 0
    . simp [M_zero]
      split
      . apply Or.inl
        let list := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
        use list[0].2
        use ⟨index.1, by omega⟩
        have in_list : list[0] ∈ list := List.getElem_mem (by assumption)
        have in_list_prop : _ := List.of_mem_filter in_list
        have : ↑index < list[0].2.1 := by aesop
        simp only [le_refl, and_true, true_and]
        omega
      . aesop
    . aesop

lemma only_swaps_or_indentity_from_makeNonZeroAtDiag_left
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : ∃ i j : Fin numVars, (makeNonZeroAtDiag M index).2 = swapColMatrix i j ∧ (index ≤ i ∧ index ≤ j) := by
  rw [makeNonZeroAtDiag]
  by_cases indeqns : numEqns ≤ index
  . simp_all only [gt_iff_lt, ge_iff_le, ↓reduceDIte, Prod.mk_one_one, Prod.snd_one]
    use index; use index; aesop (add simp same_swap_identity_2)
  . simp only [indeqns, ↓reduceDIte]
    by_cases M_zero : M ⟨↑index, by omega⟩ index ≠ 0
    . simp_all only [gt_iff_lt, ne_eq, not_false_eq_true, ↓reduceDIte, Prod.mk_one_one, Prod.snd_one]
      use index; use index; aesop (add simp same_swap_identity_2)
    . simp only [M_zero, ↓reduceDIte]
      aesop
      . use index; use index; aesop (add simp same_swap_identity_2)
      . let list := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0)) (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x)))
        use list[0].2
        use index
        have in_list : list[0] ∈ list := List.getElem_mem (by assumption)
        have in_list_prop : _ := List.of_mem_filter in_list
        have : index < list[0].2 := by aesop
        simp only [le_refl, and_true, true_and]
        omega
      . use index; use index; aesop (add simp same_swap_identity_2)


/- Proves that a applying a swap operation on rows both greater than equal two `index` preserves the `diagonalOutsideInnerBlock` property. -/
lemma diagonalOutsideInnerBlock_preserved_under_swapRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (i j : Fin numEqns)
    (h₁ : index.1 ≤ i.1) (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock ((swapRowMatrix i j) * M) index := by
  intro row col roworcol rowneqcol
  rw [swapRowMatrix_lemma, Matrix.of_apply]
  by_cases roweqi : row = i
  . simp only [roweqi, ↓reduceIte]
    have : col < index := by omega
    have : j.1 ≠ col.1 := by omega
    aesop
  . simp [roweqi]
    by_cases roweqj : row = j
    . simp [roweqj]
      have : col < index := by omega
      have : i.1 ≠ col.1 := by omega
      aesop
    . aesop

/- Same as above but with column operations. -/
lemma diagonalOutsideInnerBlock_preserved_under_swapColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (i j : Fin numVars)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (swapColMatrix i j)) index := by
  intro row col roworcol rowneqcol
  rw [swapColMatrix_lemma, Matrix.of_apply]
  by_cases coleqi : col = i
  . simp only [coleqi, ↓reduceIte]
    have : row < index.1 := by omega
    have : j.1 ≠ row.1 := by omega
    aesop
  . simp [coleqi]
    by_cases coleqj : col = j
    . simp [coleqj]
      have : row < index.1 := by omega
      have : i.1 ≠ row.1 := by omega
      aesop
    . aesop

/- If we apply `makeNonZeroAtDiag` to a matrix `M`, then it preserves the `diagonalOutsideInnerBlock` property. -/
lemma diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : let pair := makeNonZeroAtDiag M index;
      diagonalOutsideInnerBlock (pair.1 * M * pair.2) index := by
  intro pair
  aesop
  have row_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_right M index
  obtain ⟨i_row, j_row, h_row⟩ := row_assumption
  . have col_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_left M index
    obtain ⟨i_col, j_col, h_col⟩ := col_assumption
    rw [h_row.1, h_col.1]
    have row_diag : diagonalOutsideInnerBlock (swapRowMatrix i_row j_row * M) index := by
      refine diagonalOutsideInnerBlock_preserved_under_swapRowMatrix M index i_row j_row ?_ ?_ Mdiag
      . aesop
      . aesop
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_swapColMatrix)
  . aesop
    have col_assumption : _ := only_swaps_or_indentity_from_makeNonZeroAtDiag_left M index
    obtain ⟨i_col, j_col, h_col⟩ := col_assumption
    rw [h_col.1]
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_swapColMatrix)

/- The format we want a matrix to be after applying `makeNonZeroAtDiag`-/
def swapped_form
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : Prop :=
  if h : index ≥ numEqns then true
  else
    M ⟨index, by omega⟩ index ≠ 0 ∨ (∀ row : Fin numEqns, ∀ col : Fin numVars, row.1 = index ∨ col.1 = index → M row col = 0)

/-
lemma swapped_form_after_makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : swapped_form ((makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2) index := by
  --set N := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2 with eq
  by_cases h : numEqns ≤ index
  . simp [swapped_form, h]
  . simp [swapped_form, h]
    by_cases Mzero : M ⟨index.1, by omega⟩ index = 0
    . by_cases allzero : ∀ (row : Fin numEqns) (col : Fin numVars), ↑row = index.1 ∨ ↑col = index.1 → M row col = 0
      . apply Or.inr
        aesop
        intro row col roworcol
        simp [makeNonZeroAtDiag]
        simp only [h, ↓reduceDIte, Mzero, ↓reduceIte]
        aesop



    . have : makeNonZeroAtDiag M index = (1, 1) := by
        simp [makeNonZeroAtDiag]
        aesop
      aesop
-/

end SwapLemmas

section AddLemmas

lemma diagonalOutsideInnerBlock_preserved_under_AddRowTransvection
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (coef : α)
    (i j : Fin numEqns)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock ((addRowTransvection coef i j) * M) index := by
  intro row col roworcol rowneqcol
  rw [addRowTransvection_lemma, Matrix.of_apply]
  by_cases roweqi : row = i
  . simp only [roweqi, ↓reduceIte]
    have colltind : col < index.1 := by omega
    have colneqi : i.1 ≠ col.1 := by omega
    have colneqj : j.1 ≠ col.1 := by omega
    have : M i col = 0 := Mdiag i col (by omega) (colneqi)
    have : M j col = 0 := Mdiag j col (by omega) (colneqj)
    aesop
  . aesop

lemma diagonalOutsideInnerBlock_preserved_under_AddColTransvection
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (coef : α)
    (i j : Fin numVars)
    (h₁ : index.1 ≤ i.1)
    (h₂ : index.1 ≤ j.1)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (addColTransvection coef i j)) index := by
  intro row col roworcol rowneqcol
  rw [addColTransvection_lemma, Matrix.of_apply]
  by_cases coleqj : col = j
  . simp only [coleqj, ↓reduceIte]
    have rowltind : row < index.1 := by omega
    have rowneqi : row.1 ≠ i.1 := by omega
    have rowneqj : row.1 ≠ j.1 := by omega
    have : M row j = 0 := Mdiag row j (by omega) (rowneqj)
    have : M row i = 0 := Mdiag row i (by omega) (rowneqi)
    aesop
  . aesop

/- Asserts that diagonalOutsideInnerBlock is preserved when applying `zeroOutColMatrix'`. -/
lemma diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock
      ((zeroOutColMatrix' M ⟨index.1,indlteqns⟩ index.2 ) * M) index := by
  intro row col roworcol rowneqcol
  rw [zeroOutColMatrix_lemma]
  simp [Matrix.of_apply]
  apply Or.elim roworcol
  . intro rowltind
    aesop
  . intro colltind
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    aesop

/- Same as above but for `zeroOutRowMatrix`. -/
lemma diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (zeroOutRowMatrix' M index (by omega))) index := by
  intro row col roworcol rowneqcol
  rw [zeroOutRowMatrix_lemma]
  simp [Matrix.of_apply]
  apply Or.elim roworcol
  . intro rowltcol
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    aesop
  . intro rowltind
    aesop

lemma diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix_general
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (M * (zeroOutRowMatrix' M index (by omega))) index := by
  intro row col roworcol rowneqcol
  rw [zeroOutRowMatrix_lemma]
  simp [Matrix.of_apply]
  apply Or.elim roworcol
  . intro rowltcol
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    aesop
  . intro rowltind
    aesop

lemma values_unchanged_by_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : ∀ col : Fin numVars, ((zeroOutColMatrix' M ⟨col_index.1, collteqn⟩ col_index.2) * M) ⟨col_index.1, collteqn⟩ col = M ⟨col_index.1, collteqn⟩ col := by
  intro col
  simp only [zeroOutColMatrix_lemma, Matrix.of_apply]
  aesop

lemma same_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : zeroOutRowMatrix' M col_index collteqn = zeroOutRowMatrix' ((zeroOutColMatrix' M ⟨col_index.1, by omega⟩ (col_index.2)) * M) col_index collteqn := by
  --apply Matrix.ext
  --intro row col
  simp only [zeroOutRowMatrix', Matrix.add_apply, Matrix.neg_apply, id_eq, Int.reduceNeg, add_right_inj, neg_inj]
  sorry
  --aesop (add simp zeroOutRowMatrix')




end AddLemmas


lemma diagonalOutsideInnerBlock_preserved_by_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (inlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (pivotAtIndex M index) index := by
  rw [pivotAtIndex]

  aesop (add simp diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag)
  set swapped := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2

  have swapped_diag : diagonalOutsideInnerBlock swapped index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag)
  --simp [zeroOutColMatrix_lemma]
  have zero_swapped_diag : diagonalOutsideInnerBlock ((zeroOutColMatrix' swapped ⟨index.1, inlteqns⟩ (index.2)) * swapped) index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix)
  intro row col roworcol rowneqcol


  /-aesop (add simp diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag) (add simp diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix) (add simp diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix)
  have : diagonalOutsideInnerBlock ((makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2) index := diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag M index Mdiag
  set swapped := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2
  have : diagonalOutsideInnerBlock (zeroOutColMatrix ⟨↑index, by omega⟩ * swapped) index :=
    diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix swapped index inlteqns this
  set rowOper := zeroOutColMatrix ⟨↑index, by omega⟩ * swapped
  have : diagonalOutsideInnerBlock (rowOper * zeroOutRowMatrix index) index := by
    exact diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix rowOper index (by assumption)
  assumption-/

lemma diagonalOutsideInnerBlock_increased_by_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqns : index.1.succ < numEqns)
    (indltvars : index.1.succ < numVars)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : (diagonalOutsideInnerBlock (pivotAtIndex M index) ⟨index.1 + 1, by omega⟩) := by
    have pivotMdiag : diagonalOutsideInnerBlock (pivotAtIndex M index) index :=
      diagonalOutsideInnerBlock_preserved_by_pivot M index (by omega) Mdiag
    intro row col roworcol roweqcol
    simp_all only [Nat.succ_eq_add_one, ne_eq]
    simp_all only [Nat.succ_eq_add_one]
    aesop
    .




end Diagonalise

end

end MatrixElimination
