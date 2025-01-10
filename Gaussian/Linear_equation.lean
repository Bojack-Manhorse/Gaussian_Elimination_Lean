import Mathlib.Algebra.Module.Defs
import ZKLib.Data.UniPoly

namespace LinearEquation

@[ext]
structure linear_equation (len : ℕ) (α : Type) [CommRing α] [Inhabited α] where
  coefficients : Array α
  length : coefficients.size = len


/- A lemma which hopefully will be VERY useful: -/
lemma zip_index_swap {α : Type} {n : ℕ} {p q : Array α} {h₁ : p.size = n} {h₂ : q.size = n} {i : ℕ} (h : i < n) :
  (p.zip q)[i]'(by aesop) =
  ⟨p[i]'(by aesop), q[i]'(by aesop)⟩ := by
  induction i <;>
  . rcases p with ⟨⟨_ | _⟩, h₁⟩ <;>
    rcases q with ⟨⟨_ | _⟩, h₂⟩ <;> try (simp at h₁ h₂; omega)
    aesop

lemma add_zip_array_size {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α): (Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients)).size = len := by
  rw [Array.size_map, Array.size_zip, p.length, q.length]
  simp

/- Here's the addition operation on `linear_equation`: -/
instance {len : ℕ} {α : Type} [CommRing α] [Inhabited α] : Add (linear_equation len α) where
  add p q := ⟨Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients), by apply add_zip_array_size⟩

@[simp]
lemma defn_of_add_with_index {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α) (i : ℕ) (h : i < len) : (p + q).coefficients[i]'(by rw [(p + q).length]; assumption ) = (Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients))[i]'(by rw [add_zip_array_size]; assumption) := by
  rfl

@[simp]
lemma defn_of_add_no_index {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α) : (p + q).coefficients = Array.map (fun x => x.1 + x.2) (Array.zip p.coefficients q.coefficients) := by
  rfl

/- Show that we can swap `+` and `[i]` using `zip_index_swap`: -/

lemma index_is_linear {len : ℕ} {α : Type} [CommRing α] [Inhabited α]
  (p q : linear_equation len α) (i : ℕ) (h : i < len) :
  (p + q).coefficients[i]'(by rw [(p + q).length]; assumption ) = p.coefficients[i]'(by rw [p.length]; assumption ) + q.coefficients[i]'(by rw [q.length]; assumption ) := by
  simp
  rw [zip_index_swap h]
  . exact p.length
  . exact q.length

/- Since we'll need to show that adding two elements of `linear_equation len α` gives an array of length `len`: -/

lemma add_size {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α) : (p + q).coefficients.size = p.coefficients.size := by
  rw [defn_of_add_no_index, add_zip_array_size, p.length]

lemma add_size_second_argument {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α) : (p + q).coefficients.size = q.coefficients.size := by
  rw [defn_of_add_no_index, add_zip_array_size, q.length]

/- Show add is commutative: -/

theorem add_comm_lin_eqn {α : Type} [CommRing α] [Inhabited α] (p q : linear_equation len α) : p + q = q + p := by
  apply linear_equation.ext
  apply Array.ext
  . rw [defn_of_add_no_index, defn_of_add_no_index, add_zip_array_size, add_zip_array_size]
  . intro i h₁ h₂
    rw [index_is_linear, index_is_linear, add_comm]
    . rw [add_size, p.length] at h₁; assumption
    . rw [add_size, q.length] at h₂; assumption

/- Show add is associative: -/

theorem add_assoc_lin_eqn {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p q r : linear_equation len α) : p + q + r = p + (q + r) := by
  apply linear_equation.ext
  apply Array.ext
  . rw [(p + q + r).length, (p + (q + r)).length]
  . intro i h₁ h₂
    have h₃ : i < len := by
      rw [add_size, add_size, p.length] at h₁
      exact h₁
    rw [index_is_linear, index_is_linear, index_is_linear, index_is_linear, add_assoc] <;> exact h₃

/- Define the zero element: -/

instance {len : ℕ} {α : Type} [CommRing α] [Inhabited α] : Zero (linear_equation len α) where
  zero := ⟨Array.mkArray len 0, Array.size_mkArray len 0⟩

@[simp]
lemma defn_of_zero {len : ℕ} {α : Type} [CommRing α] [Inhabited α] : (0 : (linear_equation len α)).coefficients = Array.mkArray len 0 := by rfl

/- Prove stuff about the zero element -/

lemma zero_add_lin_eqn {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p : linear_equation len α) : 0 + p = p := by
  apply linear_equation.ext
  apply Array.ext
  . rw [add_size_second_argument]
  . intro i h₁ h₂
    rw [index_is_linear]
    simp
    rw [p.length] at h₂
    assumption

/- Define negation -/

instance {len : ℕ} {α : Type} [CommRing α] [Inhabited α] : Neg (linear_equation len α) where
  neg p := ⟨Array.map (fun x => -x) p.coefficients, by rw [Array.size_map, p.length]⟩

@[simp]
lemma defn_of_neg {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p : linear_equation len α) : (-p).coefficients = Array.map (fun x => -x) p.coefficients := by rfl

/- Prove stuff about negation: -/

lemma neg_add_cancel_lin_eqn {len : ℕ} {α : Type} [CommRing α] [Inhabited α] (p : linear_equation len α) : -p + p = 0 := by
  apply linear_equation.ext
  apply Array.ext
  . simp [add_size_second_argument, p.length]
  . intro i h₁ h₂
    rw [index_is_linear]
    simp
    rw [add_size_second_argument, p.length] at h₁
    assumption

def eval_poly {α : Type} [CommRing α] [Inhabited α] {len : ℕ} (poly : linear_equation len α) (pts : Vector α (len - 1)) : α :=
  (∑ i < len - 1, pts[i]! * poly.coefficients[i]!) + poly.coefficients[len - 1]!

@[simp]
lemma eval_poly_defn {α : Type} [CommRing α] [Inhabited α] {len : {x : ℕ // x > 1}} (poly : linear_equation len α) (pts : Vector α (len - 1))
    : eval_poly poly pts = (∑ i < ↑len - 1, pts[i]! * poly.coefficients[i]!) + poly.coefficients[↑len - 1]! := by rfl

/- We need to show that the set of linear equations is a module over the coefficient ring -/

lemma zip_index_pick_fst {α : Type} {n : ℕ} {p q : Array α} {h₁ : p.size = n} {h₂ : q.size = n} {i : ℕ} (h : i < n) :
  ((p.zip q)[i]'(by aesop)).1 =
  (Prod.mk (p[i]'(by aesop)) (q[i]'(by aesop))).1 := by
  rw [zip_index_swap]
  exact h
  exact h₁
  exact h₂

lemma zip_index_pick_snd {α : Type} {n : ℕ} {p q : Array α} {h₁ : p.size = n} {h₂ : q.size = n} {i : ℕ} (h : i < n) :
  ((p.zip q)[i]'(by aesop)).2 =
  (Prod.mk (p[i]'(by aesop)) (q[i]'(by aesop))).2 := by
  rw [zip_index_swap]
  exact h
  exact h₁
  exact h₂

end LinearEquation
