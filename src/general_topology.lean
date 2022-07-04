import topology.constructions
import topology.separation

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
