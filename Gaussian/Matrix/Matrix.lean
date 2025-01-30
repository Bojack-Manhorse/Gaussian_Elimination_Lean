import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.Matrix.RowCol

namespace MatrixElimination

variable {α : Type} [Field α] [Inhabited α] [DecidableEq α]

variable {numVars numEqns : ℕ}

section SystemsOfLinearEquations

/- A pair consisting of a `numEqns × numVars` matrix and a `numEqns × 1` matrix that we wish to find some vector of size `numVars × 1` that's a solution to the pair. -/
structure LinearSystem (numVars numEqns : ℕ) (α : Type) where
  vars : Matrix (Fin numEqns) (Fin numVars) α
  const : Matrix (Fin numEqns) (Fin 1) α

abbrev LinearSystem.const' (system : LinearSystem numVars numEqns α) (d : Fin numEqns) : α := system.const d 0

/- Definition of some vector `β` being a solution to some `system : linearSystem`: -/
def isSol (system : LinearSystem numVars numEqns α) (β : Matrix (Fin numVars) (Fin 1) α) : Prop :=
  system.vars * β = system.const

def has_solution (system : LinearSystem numVars numEqns α) : Prop :=
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
def swapColMatrix (i j : Fin numVars) : Matrix (Fin numVars) (Fin numVars) α :=
  1 + (- Matrix.stdBasisMatrix i i 1 + - Matrix.stdBasisMatrix j j 1)
    + (Matrix.stdBasisMatrix i j 1 + Matrix.stdBasisMatrix j i 1)

end Transvections

section TransvectionLemmas

lemma addRowTransvection_lemma (c : α) (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : (addRowTransvection c i j) * M =
      Matrix.of (fun x y =>
        if x = i then M i y + c * M j y
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp [addRowTransvection, Matrix.add_mul]
  aesop (add simp Matrix.StdBasisMatrix.mul_left_apply_same, )

lemma addColTransvection_lemma (c : α) (i j : Fin numVars) (M : Matrix (Fin numEqns) (Fin numVars) α)
    : M * (addColTransvection c i j) =
      Matrix.of (fun x y =>
        if y = j then M x j + c * M x i
        else M x y
      ) := by
  apply Matrix.ext
  intro row col
  simp [addColTransvection, Matrix.mul_add]
  aesop (add simp mul_comm) (add simp Matrix.StdBasisMatrix.mul_right_apply_same)

lemma swapRowMatrix_Lemma (i j : Fin numEqns) (M : Matrix (Fin numEqns) (Fin numVars) α)
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
      simp [ieqj]
    . intro ineqj
      simp [ineqj]
  . aesop

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

def constIndicator (x : α) : α := if x = 0 then 0 else 1

/- Definition of a `numEqns × numVars` matrix being diagonal: -/
def isDiagonal (D : Matrix (Fin numEqns) (Fin numVars) α) : Prop :=
  ∀ i : Fin numEqns, ∀ j : Fin numVars, (i.1 ≠ j.1 → D i j = 0)

instance {D : Matrix (Fin numEqns) (Fin numVars) α} [DecidableEq α] : Decidable (isDiagonal D) := by
  unfold isDiagonal; infer_instance

def parityCheckFun (system : LinearSystem numVars numEqns α) (i : Fin numEqns) : α × α :=
    if h1 : i < numVars
    then (system.vars i ⟨i.1, by omega⟩, constIndicator (system.const i 0))
    else (0, constIndicator (system.const i 0))


-- system.vars row * β = [0 , 0,0 ] * β = 0 ≠ c = system.const row

/- If `system.vars` is diagonal, then returns true if a row of `system.vars` is zero but that row of `system.const` is non-zero, meaning the system has no solutions. -/
def noSolutionDiagonal (system : LinearSystem numVars numEqns α) : Prop :=
  (0, 1) ∈ List.ofFn (parityCheckFun system)

lemma list_ofFn_mem {β : Type} (a : β) (m : ℕ) (f : Fin m → β) (i : Fin m) (aeq : a = f i) : a ∈ List.ofFn f := by
  aesop (add simp List.mem_ofFn) -- <-- Can add rules to aesop like so

section ParityCheckFunLemmas

variable {system : LinearSystem numVars numEqns α}

lemma parityCheckFun_of_pos {i : Fin numEqns} (h : i < numVars) :
  parityCheckFun system i = (system.vars i ⟨i.1, by omega⟩, constIndicator (system.const' i)) := by
  simp only [parityCheckFun, h, ↓reduceDIte, Fin.isValue]

lemma parityCheckFun_of_neg {i : Fin numEqns} (h : ¬i < numVars) :
  parityCheckFun system i = (0, constIndicator (system.const i 1)) := by
  simp only [parityCheckFun, h, ↓reduceDIte, Fin.isValue]

/- Don't to i ≥ j, do j ≤ i -/
lemma zero_below_diag_no_sol {system : LinearSystem numVars numEqns α} (h : isDiagonal system.vars) (i : Fin numEqns)
    : (i ≥ numVars ∧ system.const i 0 ≠ 0 ) → noSolutionDiagonal system := by
  rintro ⟨igeq, cnezero⟩
  rw [noSolutionDiagonal]
  refine list_ofFn_mem (0, 1) (numEqns) _ ?_ ?_
  . exact i
  . have h2 : ¬ i.1 < numVars := Nat.not_lt.mpr igeq
    rw [parityCheckFun]
    simp [h2, constIndicator]
    simp_all
    /- Aesop:
      - Can split by cases
      - Applies all simp lemmas
      - Discharges with rfl and other stuff-/
    -- aesop

lemma zero_diag_implies_zero_const {system : LinearSystem numVars numEqns α} (h1 : isDiagonal system.vars) (h2 : ¬ noSolutionDiagonal system) (i : Fin numEqns)
    : (h3 : i < numVars) → (system.vars i ⟨i.1, by omega⟩ = 0) → (system.const i 0 = 0) := by
  intro h3 h4
  rw [noSolutionDiagonal] at h2
  by_contra constneq0
  push_neg at constneq0
  have parity_zero : parityCheckFun system i = (0, 1) := by
    rw [parityCheckFun]
    simp [h3]
    apply And.intro
    . assumption
    . rw [constIndicator]
      aesop
  have zero_one_in_list : (0, 1) ∈ List.ofFn (parityCheckFun system) := by
    refine list_ofFn_mem (0, 1) (numEqns) _ ?_ ?_
    . exact i
    . exact Eq.symm parity_zero
  --pull_neg at h2
  exact h2 zero_one_in_list

end ParityCheckFunLemmas

#check [1, 2 ,4][0]

lemma list_ofFn_exits {β : Type} {list : List β} {a : β} (h : a ∈ list) : ∃ b : Fin (list.length), a = list[b] := by
  obtain ⟨n, hn⟩ := List.get_of_mem h
  use n
  exact (Eq.symm hn)

example (a b : ℕ) (n : Fin a) (h : a = b) : (Fin.cast h n).1 = n.1 := rfl

/- Verifies that if `noSolutionDiagonal system h` is true then there are no possible solutions. -/
lemma diagonal_system_has_no_solutions (system : LinearSystem numVars numEqns α) (h : isDiagonal system.vars)
    : noSolutionDiagonal system ↔ ¬ has_solution system := by
  apply Iff.intro
  . intro no_sol
    intro β
    rw [isSol]
    rw [noSolutionDiagonal] at no_sol
    apply list_ofFn_exits at no_sol
    obtain ⟨n, hn⟩ := no_sol
    --have lenn : (List.ofFn (parityCheckFun system)).length = numEqns :=
    let n_cast : Fin numEqns := Fin.cast (List.length_ofFn (parityCheckFun system)) n
    have neq : n_cast.1 = n.1 := by rfl
    have left_zero: (system.vars * β) n_cast 0 = 0 := by sorry
    have right_ne_zero: (system.const) n_cast 0 ≠ 0 := by
      simp [parityCheckFun, constIndicator] at hn
      apply Or.elim (Nat.lt_or_ge n.1 numVars)
      . intro nlt
        simp [nlt] at hn
        by_contra cont
        rw [show]
        simp [cont] at hn

    sorry
  . sorry

/- Given a system `system` such that `system.vars` is in diagonal form and it has a solution, construct some `β : Matrix (Fin numVars) (Fin 1) α` that should be a solution (i.e. `system.vars * β == system.const`). -/
def getSolDiagonal (system : LinearSystem numVars numEqns α ) /-(h1 : isDiagonal system.vars) (h2 : ¬ noSolutionDiagonal system)-/
    : Matrix (Fin numVars) (Fin 1) α :=
  Matrix.of
    (fun (i : Fin numVars) (j : Fin 1) =>
      if eqnsgeqvars : i >= numEqns then (0 : α)
      else
        let i' : Fin numEqns  := ⟨i.1, by omega⟩
        (system.const i' 0) / (system.vars i' i)
    )

/- Claimed evaluation of multiplying a diagonal matrix by a vector. -/
def diag_mul_eval (D : Matrix (Fin numEqns) (Fin numVars) α) /-(h : isDiagonal D)-/ (β : Matrix (Fin numVars) (Fin 1) α) : Matrix (Fin numEqns) (Fin 1) α :=
    Matrix.of (fun x y =>
    if h : x.1 >= numVars then 0
    else D x ⟨x.1, by omega⟩ * β ⟨x.1, by omega⟩ y)

/- Verification that `diag_mul_eval` is indeed the actual evaluation. -/
lemma diag_mul_verify (D : Matrix (Fin numEqns) (Fin numVars) α) (h : isDiagonal D) (β : Matrix (Fin numVars) (Fin 1) α)
    : D * β = diag_mul_eval D β := by
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

/- Check that the solution from `getSolDiagonal` is indeed a solution to `system`. -/
lemma check_diagonal_sol (system : LinearSystem numVars numEqns α ) (h1 : isDiagonal system.vars) (h2 : ¬ noSolutionDiagonal system)
    : isSol system (getSolDiagonal system) := by
  rw [isSol]
  rw [diag_mul_verify system.vars h1]
  rw [diag_mul_eval, getSolDiagonal]
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
        apply zero_below_diag_no_sol h1 i
        rw [Fin.fin_one_eq_zero k] at h3
        exact ⟨igenvars, h3⟩
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
      apply zero_diag_implies_zero_const h1 _ i iltvars syseq0
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

def get_solution_from_diagonalise (system : LinearSystem numVars numEqns α)
    (P_row : Matrix (Fin numEqns) (Fin numEqns) α) [Invertible P_row]
    (P_col : Matrix (Fin numVars) (Fin numVars) α) [Invertible P_col]
    : Matrix (Fin numVars) (Fin 1) α :=
  let new_system : LinearSystem numVars numEqns α := ⟨P_row * system.vars * P_col, P_row * system.const⟩
  P_col * getSolDiagonal new_system

lemma check_solution (system : LinearSystem numVars numEqns α)
    (system_has_sol : has_solution system)
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
  --generalize eq : P_row * system.vars * P_col = ls₁ at *
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
  have exists_sol_to_ls₃ : has_solution ls₃ := ⟨⅟P_col * β, sol_to_ls₃⟩
  aesop (add simp diagonal_system_has_no_solutions)

end NonDiagonalSolutions

section Diagonalise

/- From Mathlib Transvection 328. -/
def zeroOutColList (row_index : Fin numEqns) : List (Matrix (Fin numEqns) (Fin numEqns) α) :=
  List.ofFn (fun x : Fin (numEqns) =>
    if h : x = row_index then 1
    else addRowTransvection 1 row_index x)

/- From Mathlib Transvection 334. -/
def zeroOutRowList (col_index : Fin numVars) : List (Matrix (Fin numVars) (Fin numVars) α) :=
  List.ofFn (fun x : Fin (numVars) =>
    if h : x = col_index then 1
    else addColTransvection 1 col_index x)

/- Given a `system`, makes the entry at `system.vars index index` non-zero by trying column then row swaps-/
def makeNonZeroAtDiag (system : LinearSystem numVars numEqns α) (index : Fin numVars) : (Matrix (Fin numEqns) (Fin numEqns) α) × (Matrix (Fin numVars) (Fin numVars) α) :=
  if h1 : index ≥ numEqns then (1, 1)
  else if h2 : system.vars ⟨index.1, by omega⟩ index ≠ 0 then (1, 1)
  else
    let column := List.ofFn
      (fun x : Fin numEqns =>
        (system.vars x index, x))
    let column_filtered := column.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
    if geq : column_filtered.length > 0
      then (swapRowMatrix (column_filtered[0]'(geq)).2 ⟨index.1, Nat.gt_of_not_le h1⟩, 1)
    else
      let index' : Fin numEqns := ⟨index.1, by omega⟩
      let row := List.ofFn (fun x : Fin numVars => ((system.vars) index' x, x))
      let row_filtered := row.filter (fun x => (index.1 < x.2.1) ∧ x.1 ≠ 0)
      if geq : row_filtered.length > 0
        then (1, swapColMatrix (row_filtered[0]'(geq)).2 index)
      else (1, 1)




end Diagonalise


end MatrixElimination
