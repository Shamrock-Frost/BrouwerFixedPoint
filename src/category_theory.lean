import category_theory.isomorphism category_theory.concrete_category

open category_theory

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

lemma category_theory.eq_app_inv_of_app_hom_eq
  {C : Type*} [category C] [concrete_category C] {X Y : C} (f : X ≅ Y)
  {x : X} {y : Y} (H : f.hom x = y) : x = f.inv y := 
begin
  transitivity f.inv (f.hom x),
  { rw [← comp_apply, iso.hom_inv_id, id_apply] },
  { rw H }
end