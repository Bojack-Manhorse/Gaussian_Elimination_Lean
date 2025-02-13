import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic.FieldSimp

set_option maxHeartbeats 1000000

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

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

def non_zero_indicator (x : α) : α := if x = 0 then 0 else 1

def zeroOutColMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + (Matrix.stdBasisMatrix row_index row_index (non_zero_indicator (M row_index ⟨row_index.1, by omega⟩)))
    + -∑ (row : Fin numEqns), Matrix.stdBasisMatrix row row_index (M row ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)

lemma zeroOutColMatrix_lemma_when_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    (is_zero : M row_index ⟨row_index.1, by omega⟩ = 0)
    : zeroOutColMatrix' M row_index rowltvar = 1 := by
  simp [zeroOutColMatrix', non_zero_indicator, is_zero]

lemma zeroOutColMatrix_lemma'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) =
        Matrix.of (fun x y =>
          if x ≠ row_index ∧ y.1 = row_index.1 then
            - (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)
          else (1 : Matrix (Fin numEqns) (Fin numEqns) α) x y) := by
  rw [zeroOutColMatrix']
  apply Matrix.ext
  intro x y
  by_cases non_zero : M row_index ⟨row_index.1, by omega⟩ = 0
  . simp [non_zero, non_zero_indicator]
    aesop
    apply Matrix.one_apply_ne'
    have : y.1 ≠ x.1 := by omega
    aesop
  . by_cases y_row : y = row_index
    . by_cases x_row : x = row_index
      . simp [y_row, x_row, add_assoc, non_zero_indicator, non_zero]
        rw [Matrix.sum_apply row_index row_index Finset.univ _]
        subst y_row
        have almost_all_zero : ∀ c : Fin numEqns, c ≠ y → Matrix.stdBasisMatrix c y (M c ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) y y = 0 := by
          intro c c_neq_y
          aesop
        rw [Fintype.sum_eq_single y almost_all_zero, Matrix.StdBasisMatrix.apply_same]
        field_simp
      . simp [y_row, x_row]
        rw [Matrix.sum_apply x row_index Finset.univ _]
        subst y_row
        rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop), zero_add, neg_inj]
        have almost_all_zero : ∀ row : Fin numEqns, row ≠ x → Matrix.stdBasisMatrix row y (M row ⟨y.1, by omega⟩ / M y ⟨y.1, by omega⟩) x y = 0 := by
          intro row row_neq_x
          aesop
        rw [Fintype.sum_eq_single x almost_all_zero, Matrix.StdBasisMatrix.apply_same]
    . have y_neq : y.1 ≠ row_index.1 := by omega
      aesop
      rw [Matrix.StdBasisMatrix.apply_of_ne _ _ _ _ _ (by aesop)]
      simp [Matrix.sum_apply, add_assoc]
      have : ∀ c : Fin numEqns, Matrix.stdBasisMatrix c row_index (M c ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩) x y = 0 := by
        intro c
        rw [Matrix.StdBasisMatrix.apply_of_ne]
        aesop
      aesop

example (row col : Fin numEqns) (h : row ≠ col): (1 : Matrix (Fin numEqns) (Fin numEqns) α) row col = 0 := by exact Matrix.one_apply_ne' (id (Ne.symm h))

lemma zeroOutColMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) * M =
        Matrix.of (fun x y =>
          if x ≠ row_index then M x y - ((M row_index y) * (M x ⟨row_index.1, by omega⟩ / M row_index ⟨row_index.1, by omega⟩))
          else M x y) := by
  rw [zeroOutColMatrix_lemma']
  apply Matrix.ext
  intro row col
  rw [Matrix.mul_apply]
  by_cases row_eq : row = row_index
  . simp [row_eq]
    rw [Fintype.sum_eq_single row_index]
    . simp
    . intro x x_neq
      rw [Matrix.one_apply_ne' x_neq]
      ring
  . simp [row_eq]
    rw [Fintype.sum_eq_add row row_index]
    . have row_neq_fin : row.1 ≠ row_index.1 := by omega
      simp [row_neq_fin]
      ring
    . exact row_eq
    . intro x
      rintro ⟨x_row, x_row_index⟩
      have x_row_index_fin : x.1 ≠ row_index.1 := by omega
      simp [x_row_index_fin]
      apply Or.inl
      apply Matrix.one_apply_ne'
      assumption

example (p : Prop) [Decidable p] (h : ¬ p) (f g : Fin numEqns → α) : ∑ x : Fin numEqns, (if p then f x else g x) = ∑ x : Fin numEqns, f x := by apply?

example (f : Fin numEqns → α) (n m : Fin numEqns) (not_eq : n ≠ m) (f_eval : ∀ x : Fin numEqns, x ≠ n ∧ x ≠ m → f x = 0) : ∑ x : Fin numEqns, f x = f n + f m := by
  exact Fintype.sum_eq_add n m not_eq f_eval


lemma zeroOutColMatrix_lemma_when_non_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index.1 < numVars)
    (non_zero : M row_index ⟨row_index.1, by omega⟩ ≠ 0)
    : ∀ row : Fin numEqns, row ≠ row_index → (((zeroOutColMatrix' M row_index rowltvar) * M) row ⟨row_index.1, by omega⟩ = 0) := by
  intro row rowneq
  simp [zeroOutColMatrix_lemma, rowneq]
  field_simp

def zeroOutRowMatrix'
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (Matrix.stdBasisMatrix col_index col_index 1)
    + -∑ (col : Fin numVars), Matrix.stdBasisMatrix col col_index (M ⟨col_index.1, by omega⟩ col / M ⟨col_index, by omega⟩ col_index)

lemma zeroOutRowMatrix_lemma
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : (M * zeroOutRowMatrix' M col_index collteqn) =
        Matrix.of (fun x y =>
          if y ≠ col_index then M x y - ((M x col_index) * (M ⟨col_index.1, by omega⟩ y / M ⟨col_index.1, by omega⟩ col_index))
          else M x y) := by
  sorry

lemma zeroOutRowMatrix_lemma_when_non_zero
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    (non_zero : M ⟨col_index.1, by omega⟩ col_index ≠ 0)
    : ∀ col : Fin numVars, col ≠ col_index → ((M * (zeroOutRowMatrix' M col_index collteqn)) ⟨col_index.1, by omega⟩ col = 0) := by
  intro col colneq
  simp [zeroOutRowMatrix_lemma, colneq]
  field_simp

def zeroOutColMatrixInverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : Matrix (Fin numEqns) (Fin numEqns) α :=
  1 + -(Matrix.stdBasisMatrix row_index row_index 1)
    + ∑ (row : Fin numEqns), Matrix.stdBasisMatrix row row_index (M row ⟨row_index.1, by omega⟩ / M row_index ⟨row_index, by omega⟩)

lemma zeroOutColMatrixInverse_is_inverse
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowltvar : row_index < numVars)
    : (zeroOutColMatrix' M row_index rowltvar) * (zeroOutColMatrixInverse M row_index rowltvar) = 1 := by
  rw [zeroOutColMatrix', zeroOutColMatrixInverse]
  simp [Matrix.mul_add, mul_one, mul_neg, non_zero_indicator]
  ring
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

lemma makeNonZeroAtDiag_fst_identity
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (col_zero : ∀ row : Fin numEqns, row.1 ≠ index.1 → M row index = 0 )
    : (makeNonZeroAtDiag M index).1 = 1 := by
  rw [makeNonZeroAtDiag]
  split
  . rfl
  . split
    . rfl
    . set ls := (List.filter (fun x => decide (index.1 < ↑x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
      have lszero : ls.length = 0 := by
        aesop
      simp [lszero]
      have : ¬ 0 < ls.length := by aesop
      aesop

lemma list_of_Fn_get_index {β : Type}{f : Fin numEqns → β} {a : β} (a_in_list : a ∈ List.ofFn f)
    : ∃ n : Fin numEqns, a = f n := by
  rw [List.mem_ofFn] at a_in_list
  simp_all only [Set.mem_range]
  obtain ⟨w, h⟩ := a_in_list
  subst h
  simp_all only [exists_apply_eq_apply']

lemma makeNonZeroAtDiag_snd_identity
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqn : index.1 < numEqns)
    (row_zero : ∀ col : Fin numVars, col.1 ≠ index.1 → M ⟨index.1, by omega⟩ col = 0)
  : (makeNonZeroAtDiag M index).2 = 1 := by
  rw [makeNonZeroAtDiag]
  split
  . rfl
  . split
    . rfl
    . set ls := (List.filter (fun x => decide (index.1 < ↑x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x))) with eq
      by_cases len : 0 < ls.length
      . simp [len]
      . simp [len]
        set ls_row := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0))
              (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x))) with eq
        have ls_row_zero: ¬ 0 < ls_row.length := by
          simp_all
          refine List.filter_eq_nil_iff.mpr ?_
          intro a
          intro a_in_list
          have : _ := list_of_Fn_get_index a_in_list
          obtain ⟨n, n_prop⟩ := this
          simp [n_prop]
          intro ngtind
          have : n.1 ≠ index.1 := by omega
          aesop
        simp [ls_row_zero]



/- Zeroes out the entire row and column at `index` except for `M index index`. -/
def pivotAtIndex
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  if h : numEqns ≤ index.1 then
    M
  else
    if Mzero : ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0
      then M
    else
      (zeroOutColMatrix' swapped ⟨index.1, by omega⟩ (index.2)) * swapped * (zeroOutRowMatrix' swapped index (by omega))

def pivotAtIndexTuple
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : ((Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numEqns) (Fin numEqns) α)) × ((Matrix (Fin numVars) (Fin numVars) α) × (Matrix (Fin numVars) (Fin numVars) α)) :=
  let rowSwap := (makeNonZeroAtDiag M index).1
  let colSwap := (makeNonZeroAtDiag M index).2
  let swapped : Matrix (Fin numEqns) (Fin numVars) α := rowSwap * M * colSwap
  let one_eqn := (1 : Matrix (Fin numEqns) (Fin numEqns) α)
  let one_var := (1 : Matrix (Fin numVars) (Fin numVars) α)
  if h : numEqns ≤ index.1 then
    ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
  else
    if Mzero : ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0
      then ⟨⟨one_eqn, one_eqn⟩, ⟨one_var, one_var⟩⟩
    else
    ⟨⟨zeroOutColMatrix' swapped ⟨index.1, by omega⟩ (index.2),rowSwap ⟩, ⟨ colSwap, zeroOutRowMatrix' swapped index (by omega) ⟩⟩

lemma pivotAtIndex_eq_pivotAtIndexTuple
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    : pivotAtIndex M index =
      (pivotAtIndexTuple M index).1.1 * (pivotAtIndexTuple M index).1.2 * M *(pivotAtIndexTuple M index).2.1 * (pivotAtIndexTuple M index).2.2 := by
  simp [pivotAtIndex, pivotAtIndexTuple]
  aesop (add simp Matrix.mul_assoc)

/- Asserts that a matrix `M : Matrix (Fin numEqns) (Fin numVars) α` is diagonal outside the submatrix of indices greater than `index`. -/
def diagonalOutsideInnerBlock (M : Matrix (Fin numEqns) (Fin numVars) α) (index : Fin numVars )
    : Prop :=
  ∀ row : Fin numEqns, ∀ col : Fin numVars, (row.1 < index.1 ∨ col.1 < index.1) → row.1 ≠ col.1 → M row col = 0

/-
lemma diagonalOutsideInnerBlock_implies_diagonal
    (M : Matrix (Fin numEqns) (Fin numVars) α)
-/

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

lemma list_with_index_fin {β : Type} {f : Fin numEqns → β} {a : β × (Fin numEqns)}
    (a_in_list : a ∈ List.ofFn (fun x : Fin numEqns => (f x, x)))
    : a = (f a.2, a.2) := by
  obtain ⟨x, h⟩ := (List.mem_ofFn _ a).mp a_in_list
  apply Prod.fst_eq_iff.mp
  subst h
  simp_all only

/- If there exists some element on the row and column intersecting `M index index`, then after applying makeNonZeroAtDiag, we'll have a non-zero element at `M index index`. -/
lemma zero_after_makeNonZeroAtDiag
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (indlteqn : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    (exists_non_zero : ¬ ∀ row : Fin numEqns, ∀ col : Fin numVars, (index.1 ≤ row.1 ∧ index.1 ≤ col.1 ∧ (row.1 = index.1 ∨ col.1 = index.1)) → M row col = 0)
    : ((makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2) ⟨index.1, by omega⟩ index ≠ 0 := by
  push_neg at exists_non_zero
  obtain ⟨row, col, ⟨⟨rowgeind, colgeind, roworcol⟩, Mrowcol⟩⟩ := exists_non_zero
  rw [makeNonZeroAtDiag]
  have indlteqn' : ¬ index.1 ≥ numEqns := by omega
  simp [indlteqn']
  by_cases Mzero : M ⟨index.1, by omega⟩ index = 0
  . simp [Mzero]
    have colorrow : col.1 = index.1 ∨ row.1 = index.1 := by aesop
    apply Or.elim colorrow
    . intro coleqind
      have : row.1 ≠ index.1 := by
        by_contra roweqind;
        have : M row col ≠ 0 := by assumption
        have : row = ⟨index.1, by omega⟩ := by aesop
        have : col = ⟨index.1, by omega⟩ := by aesop
        have : M row col = 0 := by aesop
        aesop
      set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
      have coleqind_fin: col = ⟨index.1, by omega⟩ := by aesop
      have : (M row ⟨index.1, by omega⟩, row) ∈ (List.ofFn fun x => (M x index, x)) := list_ofFn_mem rfl
      have : row.1 > index.1 := by omega
      have : (M row ⟨index.1, by omega⟩, row) ∈ ls := by aesop
      have ls_len : ls.length > 0 := List.length_pos_of_mem this
      simp [ls_len]
      simp [swapRowMatrix_lemma, Matrix.of_apply]
      set swap_col := ls[0] with eq
      have swap_in_filter : swap_col ∈ ls := by aesop
      let f : α × (Fin numEqns) → Bool := fun x => decide (index.1 < ↑x.2) && !decide (x.1 = 0)
      have : f swap_col := List.of_mem_filter swap_in_filter
      have : swap_col.1 ≠ 0 := by aesop
      have : swap_col.2 ≠ ⟨index.1, by omega⟩ := by aesop
      have swapgtind : ⟨index.1, by omega⟩ ≠ swap_col.2  := by aesop
      simp [swapgtind]
      rw [← ne_eq]
      set g : (Fin numEqns) → α := fun x => M x index with eq
      have swap_in_list : swap_col ∈ (List.ofFn fun x => (g x, x)) := List.mem_of_mem_filter swap_in_filter
      have swap_col_value : swap_col = (g swap_col.2 , swap_col.2) := list_with_index_fin swap_in_list
      simp [g] at swap_col_value
      have : swap_col.1 = M swap_col.2 index := Prod.fst_eq_iff.mpr swap_col_value
      rw [← this]
      assumption
    . intro roweqind
      have : col.1 ≠ index := by
        by_contra coleqind
        have : M row col ≠ 0 := by assumption
        have : row = ⟨index.1, by omega⟩ := by aesop
        have : col = ⟨index.1, by omega⟩ := by aesop
        have : M row col = 0 := by aesop
        aesop
      set ls := (List.filter (fun x => decide (↑index < x.2.1) && !decide (x.1 = 0)) (List.ofFn fun x => (M x index, x)))
      by_cases ls_len : ls.length > 0
      . set swap_col := ls[0]
        sorry
        /- Repeat same argument as above-/
      . simp [ls_len]
        have roweqind_fin : row = ⟨index.1, by omega⟩ := by aesop
        set swap_row := (M ⟨index.1, by omega⟩ col, col)
        have : swap_row ∈ (List.ofFn fun x => (M ⟨index.1, by omega⟩ x, x)) := list_ofFn_mem rfl
        set ls' := (List.filter (fun x => decide (index < x.2) && !decide (x.1 = 0)) (List.ofFn fun x => (M ⟨↑index, by omega⟩ x, x))) with ls'_eq
        have : col.1 > index.1 := by omega
        have swap_row_in_ls' : swap_row ∈ ls' := by aesop
        have ls'_length: ls'.length > 0 := by exact List.length_pos_of_mem swap_row_in_ls'
        simp [ls'_length]
        set swap_row_first := ls'[0]
        have swap_row_first_in_ls' : swap_row_first ∈ ls' := by aesop
        simp [swapColMatrix_lemma, Matrix.of_apply]
        set f : α × (Fin numVars) → Bool := fun x => decide (index < x.2) && !decide (x.1 = 0) with eq_f
        have : f swap_row_first := by
          rw [ls'_eq] at swap_row_in_ls'
          apply List.of_mem_filter
          exact swap_row_first_in_ls'
        have : swap_row_first.1 ≠ 0 := by aesop
        have : index.1 < swap_row_first.2 := by aesop
        have : index.1 ≠ swap_row_first.2 := by omega
        have swap_neq : index ≠ swap_row_first.2 := fun a => this (congrArg Fin.val a)
        simp [swap_neq]
        sorry
        /- Repeat same argument as above-/
  . simp [Mzero]

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
    have rowneqind: row ≠ ⟨↑index, indlteqns⟩ := by aesop
    simp [rowneqind]
    have Mzero : M row col = 0 := by aesop
    aesop
  . intro colltind
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    split
    . assumption
    . have Mzero': M ⟨index.1, indlteqns⟩ col = 0 := by
        have indneqcol : index.1 ≠ col.1 := by omega
        specialize Mdiag (⟨index.1, by omega⟩) col (by aesop) (indneqcol)
        exact Mdiag
      rw [Mzero']
      field_simp
      assumption

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
  . intro rowltind
    have : M row col = 0 := Mdiag row col roworcol rowneqcol
    aesop
  . intro colltind
    have Mzero : M row col = 0 := Mdiag row col roworcol rowneqcol
    have colneqind: col ≠ index := by aesop
    simp [colneqind]
    have Mzero' : M ⟨index.1, by omega⟩ col = 0 := by
      have : index.1 ≠ col.1 := by omega
      specialize Mdiag ⟨index.1, by omega⟩ col (by aesop (add simp colltind)) (by assumption)
      exact Mdiag
    rw [Mzero, Mzero']
    field_simp

/- Proves that `M` and `(zeroOutColMatrix' M col_index) * M` have the same values on the `col_index` row. -/
lemma values_unchanged_by_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : ∀ col : Fin numVars, ((zeroOutColMatrix' M ⟨col_index.1, collteqn⟩ col_index.2) * M) ⟨col_index.1, collteqn⟩ col = M ⟨col_index.1, collteqn⟩ col := by
  intro col
  simp [zeroOutColMatrix_lemma]

/- Uses the previous theorem to show `zeroOutRowMatrix' _ col_index` is the same for `M` and `(zeroOutColMatrix' M col_index) * M`. -/
lemma same_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (col_index : Fin numVars)
    (collteqn : col_index < numEqns)
    : zeroOutRowMatrix' M col_index collteqn = zeroOutRowMatrix' ((zeroOutColMatrix' M ⟨col_index.1, by omega⟩ (col_index.2)) * M) col_index collteqn := by
  simp only [zeroOutRowMatrix', Matrix.add_apply, Matrix.neg_apply, id_eq, Int.reduceNeg, add_right_inj, neg_inj]
  apply Fintype.sum_congr
  intro col
  aesop (add simp values_unchanged_by_zeroOutColMatrix)

lemma values_unchanged_by_zeroOutRowMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowlteqn : row_index < numVars)
    : ∀ row : Fin numEqns, (M * (zeroOutRowMatrix' M ⟨row_index.1, by omega⟩ row_index.2)) row ⟨row_index.1, rowlteqn⟩ = M row ⟨row_index.1, by omega⟩ := by
  intro row
  simp [zeroOutRowMatrix_lemma]

lemma same_zeroOutColMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (row_index : Fin numEqns)
    (rowlteqn : row_index < numVars)
    : zeroOutColMatrix' M row_index (by omega) = zeroOutColMatrix' (M * (zeroOutRowMatrix' M ⟨row_index.1, by omega⟩ (row_index.2))) row_index (by omega) := by
  have M_eq : M row_index ⟨row_index.1, by omega⟩ = (M * zeroOutRowMatrix' M ⟨↑row_index, by omega⟩ (row_index.2)) row_index ⟨↑row_index, by omega⟩ := by
    aesop (add simp values_unchanged_by_zeroOutRowMatrix)
  by_cases non_zero : M row_index ⟨row_index.1, by omega⟩ = 0
  . simp [non_zero, add_assoc, zeroOutColMatrix_lemma_when_zero]
    rw [zeroOutColMatrix_lemma_when_zero]
    aesop
  . have non_zero': (M * zeroOutRowMatrix' M ⟨↑row_index, by omega⟩ (row_index.2)) row_index ⟨↑row_index, by omega⟩ ≠ 0 := by aesop
    simp [non_zero, non_zero', zeroOutColMatrix', non_zero_indicator, add_assoc]
    apply Fintype.sum_congr
    aesop (add simp values_unchanged_by_zeroOutRowMatrix)

end AddLemmas

section ApplyingPivot

lemma diagonalOutsideInnerBlock_preserved_by_pivot
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (index : Fin numVars)
    (inlteqns : index.1 < numEqns)
    (Mdiag : diagonalOutsideInnerBlock M index)
    : diagonalOutsideInnerBlock (pivotAtIndex M index) index := by
  rw [pivotAtIndex]
  have neindge : ¬ index.1 ≥ numEqns := by omega
  simp [neindge]
  split
  . assumption
  set swapped := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2
  have swapped_diag : diagonalOutsideInnerBlock swapped index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_makeNonZeroAtDiag)
  have zero_swapped_diag : diagonalOutsideInnerBlock ((zeroOutColMatrix' swapped ⟨index.1, inlteqns⟩ (index.2)) * swapped) index := by
    aesop (add simp diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix)
  rw [same_zeroOutRowMatrix]
  apply diagonalOutsideInnerBlock_preserved_under_zeroOutRowMatrix
  . assumption
  . apply diagonalOutsideInnerBlock_preserved_under_zeroOutColMatrix
    assumption

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
  simp [pivotAtIndex]
  have eqngtind: ¬ numEqns ≤ index.1 := by omega
  simp [eqngtind]
  split
  . aesop
    . have rowor: row.1 = index.1 ∨ row.1 < index.1 := by omega
      apply Or.elim rowor
      . intro roweqind
        aesop
        by_cases col_or : index ≤ col
        . specialize h row col (by omega) (col_or) (by aesop)
          exact h
        . aesop
      . aesop
    . have color: col.1 = index.1 ∨ col.1 < index.1 := by omega
      apply Or.elim color
      . intro coleqind
        by_cases row_or : index.1 ≤ row
        . specialize h row col (row_or) (by omega) (by aesop)
          exact h
        . aesop
      . aesop
  . set N := (makeNonZeroAtDiag M index).1 * M * (makeNonZeroAtDiag M index).2 with eq_N
    have : N ⟨index.1, by omega⟩ index ≠ 0 := by aesop (add simp zero_after_makeNonZeroAtDiag)
    rw [Matrix.mul_assoc]
    set zeroed_row := (N * zeroOutRowMatrix' N index (by omega)) with eq
    have : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = 0 := by
      intro col' col_neq
      rw [eq]
      aesop (add simp zeroOutRowMatrix_lemma_when_non_zero)
    have : zeroed_row ⟨index.1, by omega⟩ index ≠ 0 := by
      rw [eq, zeroOutRowMatrix_lemma, Matrix.of_apply]
      simp
      assumption
    set zeroed_row_col := (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (index.2)) * zeroed_row with eq'
    have row_is_eq : ∀ row' : Fin numEqns, row'.1 ≠ index.1 → zeroed_row_col row' index = 0 := by
      intro row' row_neq
      rw [eq']
      have row_neq_fin: row' ≠ ⟨index.1, by omega⟩ := by aesop
      simp [zeroOutColMatrix_lemma, Matrix.of_apply, row_neq_fin]
      field_simp
    have col_is_eq : ∀ col' : Fin numVars, col' ≠ index → zeroed_row ⟨index.1, by omega⟩ col' = zeroed_row_col ⟨index.1, by omega⟩ col' := by
      intro col' col_neq
      rw [eq', zeroOutColMatrix_lemma, Matrix.of_apply]
      simp
    apply Or.elim roworcol
    . intro rowltind1
      have rowltind: row.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le rowltind)
      . intro roweqind
        have colneqind: col ≠ index := by aesop
        specialize col_is_eq col colneqind
        rw [eq'] at col_is_eq
        have row_eq_ind_fin : row = ⟨index.1, by omega⟩ := by aesop
        rw [row_eq_ind_fin]
        have simp_N: (zeroOutColMatrix' zeroed_row ⟨index.1, by omega⟩ (by omega)) = zeroOutColMatrix' N ⟨index.1, by omega⟩ (by omega) := by
          rw [eq]
          rw [same_zeroOutColMatrix N]
          omega
        rw [← simp_N]
        simp [zeroOutColMatrix_lemma]
        rw [eq]
        simp [zeroOutRowMatrix_lemma, colneqind]
        field_simp
      . intro rowltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        specialize pivotMdiag row col (by aesop?) (by aesop)
        exact pivotMdiag
    . intro colltind1
      have colleind : col.1 ≤ index.1 := by omega
      apply Or.elim (Nat.eq_or_lt_of_le colleind)
      . intro coleqind
        rw [eq]
        rw [← Matrix.mul_assoc]
        set zeroed_col := (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2)) * N with eq'''
        have col_eq_ind_fin : col = index := by aesop
        have simp_N : zeroOutRowMatrix' zeroed_col index (by omega) = zeroOutRowMatrix' N index (by omega) := by
          rw [eq''']
          rw [same_zeroOutRowMatrix N]
        rw [← simp_N]
        simp [zeroOutRowMatrix_lemma, col_eq_ind_fin]
        rw [eq''']
        have row_neq_index : row ≠ ⟨index.1, by omega⟩ := by aesop
        simp [zeroOutColMatrix_lemma, row_neq_index]
        field_simp
      . intro colltind
        have pivot_eq : pivotAtIndex M index = (zeroOutColMatrix' N ⟨index.1, by omega⟩ (index.2) * zeroed_row) := by
          rw [pivotAtIndex]
          simp [eqngtind]
          split
          . aesop
          . rw [← eq_N]
            simp [Matrix.mul_assoc]
        rw [← pivot_eq]
        specialize pivotMdiag row col (by aesop) (by aesop)
        exact pivotMdiag

end ApplyingPivot

section ApplyDiagonalise

def diagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  Fin.foldl numVars pivotAtIndex M

def n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin numVars)
    : Matrix (Fin numEqns) (Fin numVars) α :=
  Fin.foldl n.1 (fun Mat num => pivotAtIndex M ⟨num.1, by omega⟩) M

lemma foldl_outside_succ
    (β : Type)
    (b : β)
    {n : ℕ}
    (f : β → ℕ → β)
    : Fin.foldl n (fun x y => f x y) b = b := sorry


lemma n_th_diagonal_after_n_thDiagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (n : Fin numVars)
    (n_lt_eqns : n.1 < numEqns)
    : diagonalOutsideInnerBlock (n_thDiagonaliseMatrix M n) n := by
  rw [n_thDiagonaliseMatrix]
  rcases n with ⟨n, hn⟩
  induction' n with n ih --generalizing M
  . aesop (add simp diagonalOutsideInnerBlock)
  . have fold_apply: Fin.foldl (n + 1) (fun Mat num => pivotAtIndex M ⟨num, by omega⟩) M  = pivotAtIndex (Fin.foldl (n) (fun Mat num => pivotAtIndex M ⟨num, by omega⟩) M) ⟨n, by omega⟩ := by
      --rw [Fin.foldl_succ_last]
      sorry
    rw [fold_apply]
    specialize ih (by omega) (Nat.lt_of_succ_lt n_lt_eqns)
    apply diagonalOutsideInnerBlock_increased_by_pivot
    . exact n_lt_eqns
    . aesop
    . exact ih



lemma is_diagonal_after_diagonaliseMatrix
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    (var_pos : numVars > 0)
    (eqn_pos : numEqns > 0)
    : isDiagonal (diagonaliseMatrix M) := by
  rw [diagonaliseMatrix]
  let min_eqn_var := min numEqns numVars
  have : diagonalOutsideInnerBlock (n_thDiagonaliseMatrix M ⟨min_eqn_var - 1, by omega ⟩) ⟨min_eqn_var - 1, by  omega⟩ := by
    apply n_th_diagonal_after_n_thDiagonaliseMatrix
    aesop
    omega

  intro row col rowneqcol
  sorry

/- A vector contaning all the elements to the left of M in `diagonaliseMatrix M`, specifically all the row operations. -/
def diagonalizeLeft
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Vector (Matrix (Fin numEqns) (Fin numEqns) α) (2 * numVars) :=
  sorry

lemma diagonalizeLeft_invertible
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : [Invertible (Array.foldr (· * ·) (1 : Matrix (Fin numEqns) (Fin numEqns) α) (diagonalizeLeft M).toArray)] := sorry

/- A vector containing all the elements to the right of M in `diagonaliseMatrix M`, so all the column operations. -/
def diagonalizeRight
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : Vector (Matrix (Fin numVars) (Fin numVars) α) (2 * numVars) :=
  sorry



lemma verify_diagonalize_left_right
    (M : Matrix (Fin numEqns) (Fin numVars) α)
    : diagonaliseMatrix M = (Array.foldr (· * ·) (1 : Matrix (Fin numEqns) (Fin numEqns) α) (diagonalizeLeft M).toArray) * M * (Array.foldl (· * ·) (1 : Matrix (Fin numVars) (Fin numVars) α) (diagonalizeRight M).toArray) := sorry

def get_solution_of_system
    (system : LinearSystem numEqns numVars α)
    : Matrix (Fin numVars) (Fin 1) α :=
  get_solution_from_diagonalise system

end ApplyDiagonalise


end Diagonalise

end MatrixElimination
