import topology.constructions
import topology.separation
import topology.category.Top.basic

lemma quotient_map_of_is_closed_map {α β} [topological_space α] [topological_space β] 
  (f : α → β) : function.surjective f → is_closed_map f → continuous f → quotient_map f :=
begin
  intros hS hC hCont,
  rw quotient_map_iff,
  split, assumption,
  intro U, 
  rw [← is_closed_compl_iff, ← is_closed_compl_iff, ← set.preimage_compl],
  generalize : Uᶜ = C, clear U,
  split, 
  { apply is_closed.preimage, assumption },
  { intro h, rw (_ : C = f '' (f ⁻¹' C)),
    { apply hC, assumption },
    { symmetry, apply set.image_preimage_eq_of_subset,
      rw hS.range_eq, apply set.subset_univ } }
end

lemma surjection_of_compact_hausdorff_is_quot_map {α β} [topological_space α] [topological_space β]
  [compact_space α] [t2_space β]
  (f : α → β) : function.surjective f → continuous f → quotient_map f :=
λ hSurj hCont, quotient_map_of_is_closed_map f hSurj
                                             (λ C hC, (hC.is_compact.image hCont).is_closed)
                                             hCont

noncomputable
def lift_along_quot_map {α β γ : Top} (q : α ⟶ β) (f : α ⟶ γ) (Hquot : quotient_map q)
  (H : ∀ x y, q x = q y → f x = f y) : β ⟶ γ := {
    to_fun := λ b, f (classical.some (Hquot.left b)),
    continuous_to_fun := (quotient_map.continuous_iff Hquot).mpr
                          (continuous.congr f.continuous_to_fun
                            (λ x, H x _ (eq.symm (classical.some_spec (Hquot.left (q x))))))
  }

lemma lift_along_quot_map_spec {α β γ : Top} (q : α ⟶ β) (f : α ⟶ γ) (Hquot : quotient_map q)
  (H : ∀ x y, q x = q y → f x = f y) (b : β) (a : α) (h : q a = b)
  : lift_along_quot_map q f Hquot H b = f a := 
  H (classical.some (lift_along_quot_map._proof_1 q Hquot b)) a
    ((classical.some_spec (Hquot.left b)).trans h.symm)

