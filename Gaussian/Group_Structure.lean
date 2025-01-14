import Gaussian.Linear_equation

namespace GroupStructure

open LinearEquation

variable {α : Type} [Field α] [Inhabited α] {len n : {x : ℕ // x > 1}}

instance : AddCommMonoid (linearEquation α len) where
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
  nsmul n p := ⟨Array.map (fun x => n * x) p.toArray, by rw [Array.size_map, Vector.size_toArray] ⟩
  --zsmul z p := ⟨Array.map (fun x => z * x ) p.coefficients, by rw[ Array.size_map, p.length]⟩
  nsmul_zero := by
    intro x
    apply vector_ext
    intro i
    simp [← vector_to_array_element]

  nsmul_succ := by
    intro n x
    apply vector_ext
    intros
    simp [← vector_to_array_element, zip_index_swap]
    ring

/- To show it's a module: -/

instance {len : ℕ} {α : Type} [Field α] [Inhabited α] : SMul α (linearEquation α len) where
  smul m p := ⟨Array.map (fun x => m * x) p.toArray, by rw [Array.size_map, Vector.size_toArray]⟩

@[simp]
lemma defn_of_smul {len : ℕ} {α : Type} [Field α] [Inhabited α] (m : α) (p : linearEquation α len) : (m • p).toArray = Array.map (fun x => m * x) p.toArray := by rfl

lemma add_smul_lin_eqn (r s : α) (p : (linearEquation α len)) : (r + s) • p = r • p + s • p := by
  apply vector_ext
  intro x
  simp only [defn_of_smul, defn_of_add_with_index, defn_of_smul, Array.getElem_map]
  rw [← vector_to_array_element]
  simp only [defn_of_smul]
  rw [zip_index_pick_fst _ _ (by simp) (by simp) x.1 x.2, zip_index_pick_snd _ _ (by simp) (by simp) x.1 x.2]
  simp
  ring

lemma smul_add_lin_eqn (r : α) (p q : (linearEquation α len)) : r • (p + q) = r • p + r • q := by
  apply vector_ext
  intro x
  simp only [defn_of_add_with_index, defn_of_smul, Array.getElem_map]
  rw [← vector_to_array_element]
  simp only [defn_of_smul]
  rw [zip_index_pick_fst _ _ (by simp) (by simp) x.1 x.2, zip_index_pick_snd _ _ (by simp) (by simp) x.1 x.2]
  simp only [defn_of_add_no_index, Array.map_map, Array.getElem_map, Function.comp_apply, Fin.is_lt,
    vector_to_array_element]
  rw [zip_index_pick_fst p.toArray q.toArray (by simp) (by simp) x.1 x.2, zip_index_pick_snd p.toArray q.toArray (by simp) (by simp) x.1 x.2]
  simp
  ring

instance : Module α (linearEquation α len) where
  smul m p := m • p

  one_smul p := by
    apply vector_ext_with_arrays
    apply Array.ext
    . simp
    . intros
      simp

  add_smul := add_smul_lin_eqn

  zero_smul p := by
    apply vector_ext_with_arrays
    apply Array.ext <;> simp [Vector.size_toArray]

  mul_smul r s p := by
    apply vector_ext_with_arrays
    apply Array.ext <;> simp

  smul_zero m := by
    apply vector_ext_with_arrays
    apply Array.ext <;> simp

  smul_add := smul_add_lin_eqn

end GroupStructure
