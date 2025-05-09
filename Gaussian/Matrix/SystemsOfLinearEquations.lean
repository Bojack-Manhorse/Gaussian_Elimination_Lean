import Mathlib.Data.Matrix.RowCol
import Mathlib.Tactic.FieldSimp

namespace MatrixElimination

variable {α : Type} [Field α] [DecidableEq α]

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

def hasSolution (system : LinearSystem numVars numEqns α) : Prop :=
  ∃ β : (Matrix (Fin numVars) (Fin 1) α), isSol system β

end SystemsOfLinearEquations
