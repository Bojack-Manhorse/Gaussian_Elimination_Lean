import ZKLib.Data.UniPoly
import ZKLib.Data.MlPoly
import ZKLib.Data.MvPolynomial
import Mathlib.Algebra.Module.Defs

namespace linear_equations

/-

degree of polynomials = n
number of contraints = k
have k > n

-/

-- variable (n k : ℕ) (kgen : k > n)

/-
Each constraint is a list of n real numbers
-/

-- variable (Q : Array (Array ℝ)) (qsizek : Q.size = k) (qisizen : ∀ i < k, (Q[i]!).size = n)

/- We can turn each array in Q into a multilinear polynomial: -/







end linear_equations
