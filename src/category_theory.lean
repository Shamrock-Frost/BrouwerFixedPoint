import category_theory.isomorphism category_theory.concrete_category
import category_theory.limits.shapes.equalizers
import category_theory.endomorphism
import category_theory.category.preorder data.fin.basic
import category_theory.arrow
import category_theory.category.Cat

-- Should not be here...
lemma nat.iterate_succ {α : Type*} (f : α → α)
  : ∀ (n : ℕ) (x0 : α), f^[n + 1] x0 = f (f^[n] x0)
| 0       x0 := rfl
| (n + 1) x0 := nat.iterate_succ n (f x0)

namespace category_theory

open category_theory category_theory.limits

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

lemma iso.eq_app_inv_of_app_hom_eq
  {C : Type*} [category C] [concrete_category C] {X Y : C} (f : X ≅ Y)
  {x : X} {y : Y} (H : f.hom x = y) : x = f.inv y := 
begin
  transitivity f.inv (f.hom x),
  { rw [← comp_apply, iso.hom_inv_id, id_apply] },
  { rw H }
end

lemma is_iso.eq_app_inv_of_app_hom_eq
  {C : Type*} [category C] [concrete_category C] {X Y : C} (f : X ⟶ Y) [is_iso f]
  {x : X} {y : Y} : f x = y → x = inv f y :=
  iso.eq_app_inv_of_app_hom_eq (as_iso f)

theorem is_iso.cancel_iso_inv_left {C : Type*} [category C] {X Y Z : C}
  (f : Y ⟶ X) [is_iso f] : ∀ (g g' : Y ⟶ Z), inv f ≫ g = inv f ≫ g' ↔ g = g' :=
  iso.cancel_iso_inv_left (as_iso f)

lemma parallel_pair_comp 
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  : parallel_pair f g ⋙ F = parallel_pair (F.map f) (F.map g) :=
begin
  apply category_theory.functor.hext,
  { intro u, cases u; refl },
  { intros u v i, cases u; cases v; cases i, 
    all_goals { simp },
    all_goals { refl } },
end

def parallel_pair_comp.cocone_comp_to_cocone_pair
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  (c : cocone (parallel_pair f g ⋙ F)) : cocone (parallel_pair (F.map f) (F.map g)) := {
    X := c.X,
    ι := eq_to_hom (parallel_pair_comp F f g).symm ≫ c.ι
  }

def parallel_pair_comp.cocone_pair_to_cocone_comp
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  (c : cocone (parallel_pair (F.map f) (F.map g))) : cocone (parallel_pair f g ⋙ F) := {
    X := c.X,
    ι := eq_to_hom (parallel_pair_comp F f g) ≫ c.ι
  }

def parallel_pair_comp.is_colimit_comp_to_is_colimit_pair
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  (c : cocone (parallel_pair f g ⋙ F)) (hc : is_colimit c)
  : is_colimit (parallel_pair_comp.cocone_comp_to_cocone_pair F f g c) := {
    desc := λ s, hc.desc (parallel_pair_comp.cocone_pair_to_cocone_comp F f g s),
    fac' := by { intros, refine eq.trans (category.assoc _ _ _) _, rw hc.fac',
                 refine eq.trans (category.assoc _ _ _).symm _, simp },
    uniq' := λ s m h, hc.uniq' (parallel_pair_comp.cocone_pair_to_cocone_comp F f g s) m
                               (λ u, by { refine eq.trans _ (congr_arg (λ w, nat_trans.app (eq_to_hom (parallel_pair_comp F f g)) u ≫ w) (h u)),
                                          refine eq.trans _ (category.assoc _ _ _),
                                          refine congr_arg (λ w, w ≫ m) _,
                                          refine eq.trans _ (category.assoc _ _ _),
                                          simp }) }

def parallel_pair_comp.is_colimit_pair_to_is_colimit_comp
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  (c : cocone (parallel_pair (F.map f) (F.map g))) (hc : is_colimit c)
  : is_colimit (parallel_pair_comp.cocone_pair_to_cocone_comp F f g c) := {
    desc := λ s, hc.desc (parallel_pair_comp.cocone_comp_to_cocone_pair F f g s),
    fac' := by { intros, refine eq.trans (category.assoc _ _ _) _, rw hc.fac',
                 refine eq.trans (category.assoc _ _ _).symm _, simp },
    uniq' := λ s m h, hc.uniq' (parallel_pair_comp.cocone_comp_to_cocone_pair F f g s) m
                               (λ u, by { refine eq.trans _ (congr_arg (λ w, nat_trans.app (eq_to_hom (parallel_pair_comp F f g).symm) u ≫ w) (h u)),
                                          refine eq.trans _ (category.assoc _ _ _),
                                          refine congr_arg (λ w, w ≫ m) _,
                                          refine eq.trans _ (category.assoc _ _ _),
                                          simp }) }

lemma concrete_category.pow_eq_iter {C : Type*} [category C] [concrete_category C] {X : C} (f : X ⟶ X)
  (k : ℕ) : @coe_fn _ _ concrete_category.has_coe_to_fun (f ^ k : End X) = (f^[k]) :=
begin
  ext x,
  induction k with k ih,
  { simp, refl },
  { rw nat.iterate_succ, rw ← npow_eq_pow, dsimp [monoid.npow, npow_rec], simp, congr, exact ih }
end

end category_theory