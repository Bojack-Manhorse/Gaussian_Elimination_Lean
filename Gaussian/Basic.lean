import ZKLib.Data.UniPoly
import ZKLib.Data.MlPoly
import ZKLib.Data.MvPolynomial
import Mathlib.Algebra.Module.Defs

namespace test

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

@[ext]
structure linear_equation (len : ℕ) (α : Type*) [CommRing α] [Inhabited α] where
  coefficients : Array α
  length : coefficients.size = len

/- Here's the addition operation on `linear_equation`: -/
instance add_linear_equations {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] : Add (linear_equation len α) where
  add p q := ⟨Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients), by rw [Array.size_map, Array.size_zip, p.length, q.length]; simp⟩

def add_assoc_lin_eqn {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] (p q r : linear_equation len α) : p + q + r = p + (q + r) := by
  ext
  .

def eval_poly {α : Type*} [CommRing α] [Inhabited α] {len : ℕ} (poly : linear_equation len α) (pts : Array α) : α :=
  (∑ i < len - 1, pts[i]! * poly.coefficients[i]!) + poly.coefficients[len - 1]!

/- We need to show that the set of linear equations is a module over the coefficient ring -/

instance linear_equation_add_monoid (len : ℕ) (α : Type*) [CommRing α] [Inhabited α] : AddCommGroup (linear_equation len α) where
  add p q := ⟨ Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients), by rw [Array.size_map, Array.size_zip, p.length, q.length]; simp⟩



end test
