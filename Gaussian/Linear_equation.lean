import Mathlib.Algebra.Module.Defs
import ZKLib.Data.UniPoly
import Gaussian.Utils
import Batteries.Data.Vector
import Batteries.Data.Array
import Mathlib.Data.Vector.Basic

abbrev LinearEquation (α : Type) [Field α] [Inhabited α] (num_vars : ℕ) :=
  Vector α num_vars

namespace LinearEquation

variable {α : Type} [Field α] [Inhabited α]
         {len : ℕ}

/--
I've reduced some clutter in the statement and used the `List.getElem_zip` to prove this trivially.

A lemma which hopefully will be VERY useful:
-/
lemma zip_index_swap {α : Type} {p q : Array α} {i : ℕ} (h : i < (p.zip q).size) :
  (p.zip q)[i]'(by aesop) = ⟨p[i]'(by aesop), q[i]'(by aesop)⟩ := by cases p; cases q; simp

@[simp]
lemma getElem_zipWith {α β : Type} {p q : Vector α len} {i : Fin len} {f : α → α → β} :
  (p.zipWith q f)[i] = f p[i] q[i] := by
  rcases p with ⟨p, hp⟩
  rcases q with ⟨q, hq⟩
  rcases len with _ | len
  · cases i; omega
  · rcases p with _ | _ <;> simp at hp
    rcases q with _ | _ <;> simp at hq
    rcases i with _ | i <;> simp

variable {p q : LinearEquation α len}

/--
This is (eq.map f).length = eq.length and then (zip a b).length = a.length for the appropraitely lengthed equations.
-/
-- lemma add_zip_array_size

/-
Note that `simp` does this because of `(eq.map f).length = eq.length` and `(zip a b).length = a.length`

Here's the addition operation on `linear_equation`:
-/
instance : Add (LinearEquation α len) where
  add p q := p.zipWith q (·+·)

/-
Let's keep the abstraction I think, simp undoes some of it here.
-/

-- @[simp]
-- lemma defn_of_add_with_index (p q : linearEquation α len) (i : ℕ) (h : i < len) : (p + q)[i]'(h) = (Array.map (fun x => x.1 + x.2) (p.zip q.toArray))[i]'(by rw [add_zip_array_size]; assumption) := by
--   rfl

-- @[simp]
-- lemma defn_of_add_no_index (p q : linearEquation α len) : (p + q).toArray = Array.map (fun x => x.1 + x.2) (p.zip q.toArray) := by
--   rfl

/-
Proobably not needed.
-/
-- @[simp]
-- lemma vector_to_array_element {β : Type} {num : ℕ} (p : Vector β num) (i : ℕ) (h : i < num)
--     : p.toArray[i]'(by rw [Vector.size_toArray]; exact h) = p[i]'(h) := by rfl

/- Show that we can swap `+` and `[i]` using `zip_index_swap`: -/
lemma index_is_linear {i : Fin len} : (p + q)[i] = p[i] + q[i] := getElem_zipWith

/- Since we'll need to show that adding two elements of `linearEquation α len` gives an array of length `len`: -/
@[simp]
lemma add_size (p q : linearEquation α len) : (p + q).size = p.size := by
  rw [defn_of_add_no_index, add_zip_array_size, p.size_toArray]

@[simp]
lemma add_size_second_argument (p q : linearEquation α len) : (p + q).size = q.size := by
  rw [defn_of_add_no_index, add_zip_array_size, q.size_toArray]

/- Show add is commutative: -/

/- Why does this not already exist? -/
lemma vector_ext_with_arrays {γ : Type} {number : ℕ} (p q : Vector γ number) (h : p.toArray = q.toArray) : p = q := by
  rcases p with ⟨parr, psize⟩
  rcases q with ⟨qarr, qsize⟩
  simp at *
  exact h

/- Why does this not already exist? -/
lemma vector_ext {γ : Type} {number : ℕ} (p q : Vector γ number) (h : ∀ x : Fin number, p[x.1] = q[x.1]) : p = q := by
  rcases p with ⟨parr, psize⟩
  rcases q with ⟨qarr, qsize⟩
  simp
  apply Array.ext
  simp [qsize, psize]
  intro i h1 h2
  exact h ⟨i, by rw [psize] at h1; exact h1⟩

theorem add_comm_lin_eqn (p q : linearEquation α len) : p + q = q + p := by
  apply vector_ext
  intro x
  rw [index_is_linear, index_is_linear, add_comm]

/- Show add is associative: -/

theorem add_assoc_lin_eqn (p q r : linearEquation α len) : p + q + r = p + (q + r) := by
  apply vector_ext
  intro x
  rw [index_is_linear, index_is_linear, index_is_linear, index_is_linear, add_assoc]
/- Define the zero element: -/

instance : Zero (linearEquation α len) where
  zero := ⟨Array.mkArray len 0, Array.size_mkArray len 0⟩

@[simp]
lemma defn_of_zero : (0 : (linearEquation α len)).toArray = Array.mkArray len 0 := by rfl

/- Prove stuff about the zero element -/

lemma zero_add_lin_eqn (p : linearEquation α len) : 0 + p = p := by
  apply vector_ext
  intro x
  rw [index_is_linear, ← vector_to_array_element]
  simp

/- Define negation -/

instance : Neg (linearEquation α len) where
  neg p := ⟨Array.map (fun x => -x) p.toArray, by rw [Array.size_map, p.size_toArray]⟩

@[simp]
lemma defn_of_neg (p : linearEquation α len) : (-p).toArray = Array.map (fun x => -x) p.toArray := by rfl

/- Prove stuff about negation: -/

lemma neg_add_cancel_lin_eqn (p : linearEquation α len) : -p + p = 0 := by
  apply vector_ext
  intro x
  rw [index_is_linear, ← vector_to_array_element, ← vector_to_array_element, ← vector_to_array_element]
  simp

lemma fin_less_than (m : {x : ℕ // x > 1}) : ∀ x : Fin (m - 1), ↑x < m.1 := by
  omega

def eval_poly (poly : linearEquation α len) (pts : Vector α (len - 1)) : α :=
  (∑ i : Fin (len - 1), pts[i]'(i.2) * poly[i]'(by omega) + poly[↑len - 1]'(by omega))

@[simp]
lemma eval_poly_defn (poly : linearEquation α len) (pts : Vector α (len - 1))
    : eval_poly poly pts = (∑ i : Fin (len - 1), pts[i]'(i.2) * poly[i]'(by omega) + poly[↑len - 1]'(by omega)) := by rfl

     /-eval_poly poly pts = (∑ i : Fin (len - 1), pts[i]'(i.2) * poly[i]'(fin_less_than len i)) + poly[↑len - 1]'(by omega) := by rfl-/

/- We need to show that the set of linear equations is a module over the coefficient ring -/

lemma zip_index_pick_fst {β : Type} {n : ℕ} (p q : Array β) (h₁ : p.size = n) (h₂ : q.size = n) (i : ℕ) (h : i < n) :
    ((p.zip q)[i]'(by aesop)).1 =
    (Prod.mk (p[i]'(by aesop)) (q[i]'(by aesop))).1 := by
  rw [zip_index_swap]
  exact h
  exact h₁
  exact h₂

lemma zip_index_pick_snd {β : Type} {n : ℕ} (p q : Array β) (h₁ : p.size = n) (h₂ : q.size = n) (i : ℕ) (h : i < n) :
  ((p.zip q)[i]'(by aesop)).2 =
  (Prod.mk (p[i]'(by aesop)) (q[i]'(by aesop))).2 := by
  rw [zip_index_swap]
  exact h
  exact h₁
  exact h₂

end LinearEquation
