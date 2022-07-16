import category_theory.isomorphism category_theory.concrete_category

open category_theory

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

lemma category_theory.iso.eq_app_inv_of_app_hom_eq
  {C : Type*} [category C] [concrete_category C] {X Y : C} (f : X ≅ Y)
  {x : X} {y : Y} (H : f.hom x = y) : x = f.inv y := 
begin
  transitivity f.inv (f.hom x),
  { rw [← comp_apply, iso.hom_inv_id, id_apply] },
  { rw H }
end

lemma category_theory.is_iso.eq_app_inv_of_app_hom_eq
  {C : Type*} [category C] [concrete_category C] {X Y : C} (f : X ⟶ Y) [is_iso f]
  {x : X} {y : Y} : f x = y → x = inv f y :=
  category_theory.iso.eq_app_inv_of_app_hom_eq (as_iso f)

theorem category_theory.is_iso.cancel_iso_inv_left {C : Type*} [category C] {X Y Z : C}
  (f : Y ⟶ X) [is_iso f] : ∀ (g g' : Y ⟶ Z), inv f ≫ g = inv f ≫ g' ↔ g = g' :=
  category_theory.iso.cancel_iso_inv_left (as_iso f)