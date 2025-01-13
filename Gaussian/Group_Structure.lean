import Gaussian.Linear_equation

namespace GroupStructure

open LinearEquation

variable {α : Type} [Field α] [Inhabited α] {len n : {x : ℕ // x > 1}}

instance : AddCommMonoid (linear_equation len α) where
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

lemma add_smul_lin_eqn (r s : α) (p : (linear_equation len α)) : (r + s) • p = r • p + s • p := by
  apply linear_equation.ext
  apply Array.ext
  . simp
  . intro i h₁ h₂
    rw [((r + s) • p).length] at h₁
    simp
    rw [zip_index_pick_fst _ _ (by rw [Array.size_map, p.length]) (by rw [Array.size_map, p.length]) i h₁, zip_index_pick_snd _ _ (by rw [Array.size_map, add_size, (r • p).length, p.length]) (by rw [Array.size_map, add_size, (r • p).length, p.length]) i h₂]
    simp
    ring


lemma smul_add_lin_eqn (r : α) (p q : (linear_equation len α)) : r • (p + q) = r • p + r • q := by
  apply linear_equation.ext
  apply Array.ext
  . simp
  . intro i h₁ h₂
    have h : i < ↑len := by rw [(r • (p + q)).length] at h₁; exact h₁
    simp
    rw [zip_index_pick_fst p.coefficients _ p.length q.length i h, zip_index_pick_snd _ q.coefficients p.length q.length i h]
    rw [zip_index_pick_fst _ _ (by rw [Array.size_map, p.length]) (by rw [Array.size_map, q.length]) i h, zip_index_pick_snd _ _ (by rw [Array.size_map, p.length]) (by rw [Array.size_map, q.length]) i h]
    simp
    ring

instance : Module α (linear_equation len α) where
  smul m p := m • p

  one_smul p := by
    apply linear_equation.ext
    apply Array.ext
    . simp
    . intros
      simp

  add_smul := add_smul_lin_eqn

  zero_smul p := by
    apply linear_equation.ext
    apply Array.ext <;> simp [p.length]

  mul_smul r s p := by
    apply linear_equation.ext
    apply Array.ext <;> simp

  smul_zero m := by
    apply linear_equation.ext
    apply Array.ext <;> simp

  smul_add := smul_add_lin_eqn

end GroupStructure
