import Gaussian.Linear_equation

namespace GroupStructure

open LinearEquation

instance (len : ℕ) (α : Type) [Field α] [Inhabited α] : AddCommMonoid (linear_equation len α) where
  add p q := p + q
  zero := 0
  --neg p := -p
  add_assoc := add_assoc_lin_eqn
  add_comm := add_comm_lin_eqn
  zero_add := zero_add_lin_eqn
  --neg_add_cancel := neg_add_cancel_lin_eqn
  add_zero := by
    intro a
    rw [add_comm_lin_eqn a 0]
    exact zero_add_lin_eqn a
  nsmul n p := ⟨Array.map (fun x => n * x) p.coefficients, by rw [Array.size_map, p.length]; ⟩
  --zsmul z p := ⟨Array.map (fun x => z * x ) p.coefficients, by rw[ Array.size_map, p.length]⟩
  nsmul_zero := by
    intro x
    apply linear_equation.ext
    apply Array.ext
    . rw [Array.size_map, linear_equation.length, linear_equation.length]
    . intros
      simp
  nsmul_succ := by
    intro n x
    apply linear_equation.ext
    apply Array.ext
    . rw [Array.size_map, linear_equation.length, linear_equation.length]
    . intro i h₁ h₂
      simp [x.length] at h₁
      simp
      rw [zip_index_swap h₁]
      simp
      ring
      rw [Array.size_map, x.length]
      rw [x.length]

/- To show it's a module: -/

instance {len : ℕ} {α : Type} [Field α] [Inhabited α] : SMul α (linear_equation len α) where
  smul m p := ⟨Array.map (fun x => m * x) p.coefficients, by rw [Array.size_map, p.length]⟩

@[simp]
lemma defn_of_smul {len : ℕ} {α : Type} [Field α] [Inhabited α] (m : α) (p : linear_equation len α) : (m • p).coefficients = Array.map (fun x => m * x) p.coefficients := by rfl



instance (len : ℕ) (α : Type) [Field α] [Inhabited α] : Module α (linear_equation len α) where
  smul m p := m • p

  one_smul p := by
    apply linear_equation.ext
    apply Array.ext
    . simp
    . intros
      simp

  add_smul r s p := by
    apply linear_equation.ext
    apply Array.ext
    . simp
    . --intro i h₁ h₂
      --rw [((r + s) • p).length] at h₁
      simp
      rw [zip_index_pick_fst, zip_index_pick_snd h₁]
      simp
      ring
      rw [Array.size_map, p.length]
      rw [Array.size_map, p.length]
      rw [Array.size_map, p.length]
      rw [Array.size_map, p.length]

  zero_smul p := by
    apply linear_equation.ext
    apply Array.ext <;> simp [p.length]

  mul_smul r s p := by
    apply linear_equation.ext
    apply Array.ext <;> simp

  smul_zero m := by
    apply linear_equation.ext
    apply Array.ext <;> simp

  smul_add r p q := by
    apply linear_equation.ext
    apply Array.ext
    . simp
    . simp
      rw [zip_index_pick_snd, zip_index_pick_fst]



instance (len : ℕ) (α : Type) [Field α] [Inhabited α] : Module α (linear_equation len α) where

end GroupStructure