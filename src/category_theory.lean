import category_theory.isomorphism category_theory.concrete_category.unbundled_hom
import category_theory.limits.shapes.equalizers
import category_theory.endomorphism
import category_theory.category.preorder data.fin.basic
import category_theory.arrow
import category_theory.category.Cat
import category_theory.limits.presheaf
import category_theory.limits.comma
import data.setoid.basic

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

def parallel_pair_comp
  {C : Type*} {D : Type*} [category C] [category D] (F : C ⥤ D) {X Y : C} (f g : X ⟶ Y)
  : parallel_pair f g ⋙ F ≅ parallel_pair (F.map f) (F.map g) := {
    hom := {
      app := λ i, walking_parallel_pair.rec_on i (𝟙 (F.obj X)) (𝟙 (F.obj Y)),
      naturality' := by {
        intros i j f, cases f; dsimp;
        simp only [category.comp_id, category.id_comp,
                   eq_self_iff_true, functor.map_id] } },
    inv := {
      app := λ i, walking_parallel_pair.rec_on i (𝟙 (F.obj X)) (𝟙 (F.obj Y)),
      naturality' := by {
        intros i j f, cases f; dsimp;
        simp only [category.comp_id, category.id_comp,
                   eq_self_iff_true, functor.map_id] } },
    hom_inv_id' := by { ext j, cases j; apply category.id_comp },
    inv_hom_id' := by { ext j, cases j; apply category.id_comp }
  }

def limits.types.quotient_cocone {X : Type*} (s : setoid X) 
  : @cofork _ _ (subtype s.rel.uncurry) X
            (_root_.prod.fst ∘ subtype.val) (_root_.prod.snd ∘ subtype.val) :=
  cofork.of_π (@quotient.mk X s) 
              (by { ext x, rcases x with ⟨⟨a, b⟩, h⟩, exact quotient.sound h })

def limits.types.quotient_cocone_is_colimit {X : Type*} (s : setoid X) 
  : is_colimit (limits.types.quotient_cocone s) := {
    desc := λ c, quot.lift (cofork.π c) (λ (a b : X) (h : s.rel a b), by {
      have := congr_fun (cofork.condition c) ⟨(a, b), h⟩, exact this,
    }),
    fac' := λ c j, by {
      cases j,
      { ext a,
        simp only [cofork.condition, cofork.app_zero_eq_comp_π_left],
        refl },
      { ext, refl } },
    uniq' := by {
      intros, ext ⟨x⟩, 
      specialize w walking_parallel_pair.one,
      dsimp at ⊢ w,
      exact congr_fun w x
    }
  }

lemma concrete_category.pow_eq_iter {C : Type*} [category C] [concrete_category C] {X : C} (f : X ⟶ X)
  (k : ℕ) : @coe_fn _ _ concrete_category.has_coe_to_fun (f ^ k : End X) = (f^[k]) :=
begin
  ext x,
  induction k with k ih,
  { simp },
  { rw nat.iterate_succ, rw ← npow_eq_pow, dsimp [monoid.npow, npow_rec], simp, congr, exact ih }
end

universe u
def restricted_yoneda_functor {C : Type u} [small_category C] {ℰ : Type*} [category ℰ]
  : (C ⥤ ℰ)ᵒᵖ ⥤ ℰ ⥤ Cᵒᵖ ⥤ Type u := 
  category_theory.functor.op_hom _ _
  ⋙ whiskering_left Cᵒᵖ ℰᵒᵖ (Type u)
  ⋙ (whiskering_left _ _ _).obj yoneda

lemma restricted_yoneda_functor_obj {C : Type u} [small_category C] {ℰ : Type*} [category ℰ]
  (A : C ⥤ ℰ) : restricted_yoneda_functor.obj (opposite.op A) = colimit_adj.restricted_yoneda A := rfl

def functor.map_cone_comp {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
  : cones.functoriality K (F ⋙ G)
  ≅ cones.functoriality K F
    ⋙ cones.functoriality (K ⋙ F) G
    ⋙ cones.postcompose (functor.associator K F G).hom :=
begin
  refine nat_iso.of_components _ _,
  { intro c, refine category_theory.limits.cones.ext (iso.refl _) _,
    intro j, symmetry, exact eq.trans (category.id_comp _) (category.comp_id _) },
  { intros c c' f, ext,
    exact eq.trans (category.comp_id _) (category.id_comp _).symm }
end

def functor.map_cone_map_cone {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
  : cones.functoriality K (F ⋙ G) ⋙ cones.postcompose (functor.associator K F G).inv
  ≅ cones.functoriality K F ⋙ cones.functoriality (K ⋙ F) G :=
  ((whiskering_right _ _ _).obj (cones.postcompose (functor.associator K F G).inv)).map_iso
    (functor.map_cone_comp K F G)
  ≪≫ ((whiskering_right _ _ _).obj (cones.postcompose (functor.associator K F G).inv)).map_iso
        (functor.associator (cones.functoriality K F) (cones.functoriality (K ⋙ F) G)
                            (cones.postcompose (K.associator F G).hom)).symm
  
  ≪≫ (functor.associator _ _ _)
  ≪≫ ((whiskering_left _ _ _).obj _).map_iso
        ((limits.cones.postcompose_comp _ _).symm ≪≫
          by { rw (K.associator F G).hom_inv_id, exact limits.cones.postcompose_id })
  ≪≫ (functor.right_unitor _)

def functor.map_cone_comp' {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (c : cone K)
  : (F ⋙ G).map_cone c
  ≅ (cones.postcompose (functor.associator K F G).hom).obj (G.map_cone (F.map_cone c)) :=
  ((evaluation _ _).obj c).map_iso (functor.map_cone_comp K F G)

def functor.map_cone_map_cone' {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (c : cone K)
  : (cones.postcompose (functor.associator K F G).inv).obj ((F ⋙ G).map_cone c)
  ≅ G.map_cone (F.map_cone c) :=
  ((evaluation _ _).obj c).map_iso (functor.map_cone_map_cone K F G)

def functor.map_cocone_comp {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
  : cocones.functoriality K (F ⋙ G)
  ≅ cocones.functoriality K F
    ⋙ cocones.functoriality (K ⋙ F) G
    ⋙ cocones.precompose (functor.associator K F G).hom :=
begin
  refine nat_iso.of_components _ _,
  { intro c, refine category_theory.limits.cocones.ext (iso.refl _) _,
    intro j,
    exact eq.trans (category.comp_id _) (category.id_comp _).symm },
  { intros c c' f, ext,
    exact eq.trans (category.comp_id _) (category.id_comp _).symm }
end

def functor.map_cocone_map_cocone {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E)
  : cocones.functoriality K (F ⋙ G) ⋙ cocones.precompose (functor.associator K F G).inv
  ≅ cocones.functoriality K F ⋙ cocones.functoriality (K ⋙ F) G :=
  ((whiskering_right _ _ _).obj (cocones.precompose (functor.associator K F G).inv)).map_iso
    (functor.map_cocone_comp K F G)
  ≪≫ ((whiskering_right _ _ _).obj (cocones.precompose (functor.associator K F G).inv)).map_iso
        (functor.associator (cocones.functoriality K F) (cocones.functoriality (K ⋙ F) G)
                            (cocones.precompose (K.associator F G).hom)).symm
  
  ≪≫ (functor.associator _ _ _)
  ≪≫ ((whiskering_left _ _ _).obj _).map_iso
        ((limits.cocones.precompose_comp _ _).symm ≪≫
          by { rw (K.associator F G).inv_hom_id, exact limits.cocones.precompose_id })
  ≪≫ (functor.right_unitor _)

def functor.map_cocone_comp' {J C D E : Type*} [category J] [category C] [category D] [category E]
  (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (c : cocone K)
  : (F ⋙ G).map_cocone c
  ≅ (cocones.precompose (functor.associator K F G).hom).obj (G.map_cocone (F.map_cocone c)) :=
  ((evaluation _ _).obj c).map_iso (functor.map_cocone_comp K F G)

def functor.map_cocone_map_cocone' {J C D E : Type*} [category J] [category C] [category D]
  [category E] (K : J ⥤ C) (F : C ⥤ D) (G : D ⥤ E) (c : cocone K)
  : (cocones.precompose (functor.associator K F G).inv).obj ((F ⋙ G).map_cocone c)
  ≅ G.map_cocone (F.map_cocone c) :=
  ((evaluation _ _).obj c).map_iso (functor.map_cocone_map_cocone K F G)

def category_theory.limits.preserves_limits_of_equiv_domain {C : Type*} [category C]
  {D : Type*} [category D] {J : Type*} [category J] {K : J ⥤ C}
  {C' : Type*} [category C'] (F : C ⥤ D) (e : C ≌ C')
  (h : preserves_limit (K ⋙ e.functor) (e.inverse ⋙ F))
  : preserves_limit K F :=
begin
  constructor, intros c hc,
  let α : K ⋙ F ≅ (K ⋙ e.functor) ⋙ (e.inverse ⋙ F) :=
  calc K ⋙ F ≅ K ⋙ (𝟭 C ⋙ F) : ((whiskering_left _ _ _).obj K).map_iso F.left_unitor.symm
          ... ≅ K ⋙ ((e.functor ⋙ e.inverse) ⋙ F) : ((whiskering_left _ _ _).obj K).map_iso
                                                          (((whiskering_right _ _ _).obj F).map_iso
                                                            e.unit_iso)
          ... ≅ K ⋙ (e.functor ⋙ (e.inverse ⋙ F)) : ((whiskering_left _ _ _).obj K).map_iso 
                                                          (functor.associator _ _ _)
          ... ≅ (K ⋙ e.functor) ⋙ (e.inverse ⋙ F) : functor.associator _ _ _,
  refine is_limit.equiv_of_nat_iso_of_iso α.symm
                                          ((e.inverse ⋙ F).map_cone (e.functor.map_cone c))
                                          (F.map_cone c) _ _,
  { ext, swap, { exact F.map_iso (e.unit_iso.app c.X).symm },
    { dsimp,
      refine eq.trans (congr_arg _ (category.id_comp _))
               (eq.trans (congr_arg _ (category.id_comp _))
                 (eq.trans (congr_arg _ (category.comp_id _)) _)),
      rw [← F.map_comp, ← F.map_comp],
      refine congr_arg _ _,
      rw [← functor.comp_map],
      apply e.unit_iso.inv.naturality } },
  { destruct h, intros h' _, refine h' _,
    destruct adjunction.is_equivalence_preserves_limits e.functor, intros h'' _,
    destruct h'', intros h''' _, destruct @h''' K, intros H _,
    exact H hc, }
end.

def category_theory.limits.preserves_colimits_of_equiv_domain {C : Type*} [category C]
  {D : Type*} [category D] {J : Type*} [category J] {K : J ⥤ C}
  {C' : Type*} [category C'] (F : C ⥤ D) (e : C ≌ C')
  (h : preserves_colimit (K ⋙ e.functor) (e.inverse ⋙ F))
  : preserves_colimit K F :=
begin
  constructor, intros c hc,
  let α : K ⋙ F ≅ (K ⋙ e.functor) ⋙ (e.inverse ⋙ F) :=
  calc K ⋙ F ≅ K ⋙ (𝟭 C ⋙ F) : ((whiskering_left _ _ _).obj K).map_iso F.left_unitor.symm
          ... ≅ K ⋙ ((e.functor ⋙ e.inverse) ⋙ F) : ((whiskering_left _ _ _).obj K).map_iso
                                                          (((whiskering_right _ _ _).obj F).map_iso
                                                            e.unit_iso)
          ... ≅ K ⋙ (e.functor ⋙ (e.inverse ⋙ F)) : ((whiskering_left _ _ _).obj K).map_iso 
                                                          (functor.associator _ _ _)
          ... ≅ (K ⋙ e.functor) ⋙ (e.inverse ⋙ F) : functor.associator _ _ _,
  refine is_colimit.equiv_of_nat_iso_of_iso α.symm
                                            ((e.inverse ⋙ F).map_cocone (e.functor.map_cocone c))
                                            (F.map_cocone c) _ _,
  { ext, swap, { exact F.map_iso (e.unit_iso.app c.X).symm },
    { dsimp,
      refine eq.trans (congr_arg2 _ (congr_arg2 _ (category.comp_id _) rfl) rfl)  _,
      refine eq.trans (congr_arg2 _ (congr_arg2 _ (category.comp_id _) rfl) rfl)  _,
      refine eq.trans (congr_arg2 _ (congr_arg2 _ (category.id_comp _) rfl) rfl)  _,
      rw [← F.map_comp, ← F.map_comp],
      refine congr_arg _ _,
      rw [← functor.comp_map],
      rw ← e.unit_iso.hom.naturality, simp } },
  { destruct h, intros h' _, refine h' _,
    destruct adjunction.is_equivalence_preserves_colimits e.functor, intros h'' _,
    destruct h'', intros h''' _, destruct @h''' K, intros H _,
    exact H hc, }
end.

def category_theory.limits.preserves_colimits_of_equiv_codomain {C : Type*} [category C]
  {D : Type*} [category D] {J : Type*} [category J] {K : J ⥤ C}
  {D' : Type*} [category D'] (F : C ⥤ D) (e : D ≌ D')
  (h : preserves_colimit K (F ⋙ e.functor))
  : preserves_colimit K F :=
  @limits.preserves_colimit_of_nat_iso _ _ _ _ _ _ _ _ _
    (functor.associator _ _ _ ≪≫ ((whiskering_left _ _ _).obj F).map_iso e.unit_iso.symm
                              ≪≫ functor.right_unitor _)
    (@limits.comp_preserves_colimit C _ D' _ J _ K D _ (F ⋙ e.functor) e.inverse h _)

def category_theory.iso_to_equiv {C : Type*} [category C] {D : Type*} [category D]
  (F : Cat.of C ≅ Cat.of D) : C ≌ D :=
  ⟨F.hom, F.inv, eq_to_iso (F.hom_inv_id.symm), eq_to_iso (F.inv_hom_id),
   by { intro, simp, rw category_theory.eq_to_hom_map, simp, refl }⟩.

lemma colimit_iso_colimit_cocone_desc {J C : Type*} [category J] [category C]
  (F : J ⥤ C) [has_colimit F] (c : colimit_cocone F) (c' : cocone F)
  : (colimit.iso_colimit_cocone c).inv ≫ colimit.desc F c' = c.is_colimit.desc c' :=
 by { apply c.is_colimit.hom_ext, intro j, simp }

end category_theory
