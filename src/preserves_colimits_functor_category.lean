import category_theory.limits.functor_category
import category_theory.limits.preserves.shapes.binary_products
import category_theory.limits.yoneda
import category_theory.limits.presheaf

/-!
# Preservation of colimits in the functor category

The idea of the proof is simply that colimits in the functor category are computed
pointwise.

# References

https://ncatlab.org/nlab/show/commutativity+of+limits+and+colimits#preservation_by_functor_categories_and_localizations

-/

universes v₁ v₂ u u₂

noncomputable theory

namespace category_theory

open category limits

variables {C : Type u} [category.{v₁} C]
variables {D : Type u₂} [category.{u} D]
variables {E : Type u} [category.{v₂} E]

instance whiskering_right_preserves_colimits_of_shape {C : Type u} [category C]
  {D : Type*} [category.{u} D] {E : Type*} [category.{u} E]
  {J : Type u} [small_category J] [has_colimits_of_shape J D]
    (F : D ⥤ E) [preserves_colimits_of_shape J F] :
  preserves_colimits_of_shape J ((whiskering_right C D E).obj F) := ⟨λ K, ⟨λ c hc,
begin
  apply evaluation_jointly_reflects_colimits,
  intro k,
  change is_colimit (((evaluation _ _).obj k ⋙ F).map_cocone c),
  exact preserves_colimit.preserves hc,
end ⟩⟩

instance whiskering_right_preserves_colimits {C : Type u} [category C]
  {D : Type*} [category.{u} D] {E : Type*} [category.{u} E] (F : D ⥤ E)
  [has_colimits D] [preserves_colimits F] : preserves_colimits ((whiskering_right C D E).obj F) := ⟨⟩

end category_theory