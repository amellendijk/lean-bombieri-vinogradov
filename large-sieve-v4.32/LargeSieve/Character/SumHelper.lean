import Mathlib.NumberTheory.DirichletCharacter.GaussSum

open Finset BigOperators

noncomputable section

/-- For a MulChar on a GroupWithZero, ∑ χ(a)*g(a) = ∑_{units} χ(a)*g(a). -/
lemma mulChar_weighted_sum_eq_units
    {G₀ : Type*} [CommGroupWithZero G₀] [Fintype G₀] [DecidableEq G₀]
    {R' : Type*} [CommRing R'] [IsDomain R']
    (χ : MulChar G₀ R') (g : G₀ → R') :
    ∑ a : G₀, χ a * g a = ∑ u : G₀ˣ, χ ↑u * g ↑u := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : G₀))]
  simp only [MulChar.map_zero, zero_mul, zero_add]
  symm
  exact Finset.sum_nbij' (fun (u : G₀ˣ) => (↑u : G₀))
    (fun (a : G₀) => if h : a ≠ 0 then h.isUnit.unit else 1)
    (fun u _ => Finset.mem_erase.mpr ⟨u.ne_zero, Finset.mem_univ _⟩)
    (fun _ _ => Finset.mem_univ _)
    (fun u _ => by rw [dif_pos u.ne_zero]; exact Units.val_injective u.ne_zero.isUnit.unit_spec)
    (fun a ha => by
      have hne := (Finset.mem_erase.mp ha).1
      simp [dif_pos hne])
    (fun _ _ => rfl)

end
