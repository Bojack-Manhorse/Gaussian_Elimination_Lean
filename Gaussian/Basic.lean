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

@[ext]
structure linear_equation (len : ℕ) (α : Type*) [CommRing α] [Inhabited α] where
  coefficients : Array α
  length : coefficients.size = len

lemma add_zip_array_size {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] (p q : linear_equation len α): (Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients)).size = len := by
  rw [Array.size_map, Array.size_zip, p.length, q.length]
  simp


/- Here's the addition operation on `linear_equation`: -/
instance {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] : Add (linear_equation len α) where
  add p q := ⟨Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients), by apply add_zip_array_size⟩

@[simp]
lemma defn_of_add_with_index {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] (p q : linear_equation len α) (i : ℕ) (h : i < len) : (p + q).coefficients[i]'(by rw [(p + q).length]; assumption ) = (Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients))[i]'(by rw [add_zip_array_size]; assumption) := by
  rfl

lemma defn_of_add_no_index {α : Type*} [CommRing α] [Inhabited α] (p q : linear_equation len α) : (p + q).coefficients = Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients) := by
  rfl


lemma index_is_linear {len : ℕ} {α : Type*} [CommRing α] [Inhabited α]
  (p q : linear_equation len α) (i : ℕ) (h : i < len) :
  (p + q).coefficients[i]'(by rw [(p + q).length]; assumption ) = p.coefficients[i]'(by rw [p.length]; assumption ) + q.coefficients[i]'(by rw [q.length]; assumption ) := by
  sorry

theorem add_assoc_lin_eqn {len : ℕ} {α : Type*} [CommRing α] [Inhabited α] (p q r : linear_equation len α) : p + q + r = p + (q + r) := by
  ext
  . rw [(p + q + r).length, (p + (q + r)).length]
  . sorry

lemma add_zip_split_index {α : Type*} [CommRing α] [Inhabited α] (p q : Array α) (h : p.size = q.size) (i : ℕ) (h₂ : i < p.size) : (Array.map (fun x => x.1 + x.2) (Array.zip p q))[i]'(by rw [Array.size_map, Array.size_zip, ← h]; simp; assumption ) = p[i]'h₂ + q[i]'(by rw [← h]; assumption) := by
  simp




lemma add_zip_comm {α : Type*} [CommRing α] [Inhabited α] (p q : Array α) : Array.map (fun x => x.1 + x.2) (p.zip q) = Array.map (fun x => x.1 + x.2) (q.zip p) := by
  ext
  . simp only [Array.size_map, Array.size_zip]
    exact Nat.min_comm p.size q.size
  .

theorem add_comm_lin_eqn {α : Type*} [CommRing α] [Inhabited α] (p q : linear_equation len α) : p + q = q + p := by
  ext
  . rw [defn_of_add_no_index, defn_of_add_no_index, add_zip_array_size, add_zip_array_size]
  . rw [defn_of_add_with_index, defn_of_add_with_index]

lemma array_add_size {α : Type*} [CommRing α] [Inhabited α] {len : ℕ} (p q : Array α) (h₁ : p.size = len) (h₂ : q.size = len) : (Array.map (fun x => x.1 + x.2) (Array.zip p q)).size = len := by
  rw [Array.size_map, Array.size_zip, h₁, h₂]
  simp

def eval_poly {α : Type*} [CommRing α] [Inhabited α] {len : ℕ} (poly : linear_equation len α) (pts : Array α) : α :=
  (∑ i < len - 1, pts[i]! * poly.coefficients[i]!) + poly.coefficients[len - 1]!

/- We need to show that the set of linear equations is a module over the coefficient ring -/

instance linear_equation_add_monoid (len : ℕ) (α : Type*) [CommRing α] [Inhabited α] : AddCommGroup (linear_equation len α) where
  add p q := ⟨ Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients), by rw [Array.size_map, Array.size_zip, p.length, q.length]; simp⟩

end linear_equations
