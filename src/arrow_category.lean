import category_theory.arrow category_theory.category.Cat category_theory.abelian.transfer
import category_theory.limits.shapes.functor_category category_theory.limits.preserves.shapes.zero
import category_theory.abelian.functor_category
import algebra.homology.homology
import .category_theory

open category_theory

inductive walking_arrow
| source | target

inductive walking_arrow_hom : walking_arrow → walking_arrow → Type*
| id : Π {x : walking_arrow}, walking_arrow_hom x x
| arr : walking_arrow_hom walking_arrow.source walking_arrow.target

open walking_arrow walking_arrow_hom

def walking_arrow.comp : Π {x y z : walking_arrow},
  walking_arrow_hom x y → walking_arrow_hom y z → walking_arrow_hom x z
| _ _ _ id  id  := id
| _ _ _ id  arr := arr
| _ _ _ arr id  := arr

instance : small_category walking_arrow := {
  hom := walking_arrow_hom,
  id := λ x, walking_arrow_hom.id,
  comp := @walking_arrow.comp,
  id_comp' := by { intros X Y f, cases f; refl },
  comp_id' := by { intros X Y f, cases f; refl },
  assoc' := by { intros W X Y Z f g h, cases f; cases g; cases h; refl }
}

def walking_arrow.morphism_to_functor_obj {C : Type*} [category C] {x y : C} (f : x ⟶ y)
  : walking_arrow → C
| source := x
| target := y

def walking_arrow.morphism_to_functor_map {C : Type*} [category C] {x y : C} (f : x ⟶ y)
  : Π {a b : walking_arrow}, (a ⟶ b)
                           → (walking_arrow.morphism_to_functor_obj f a
                             ⟶ walking_arrow.morphism_to_functor_obj f b)
| _ _ id  := 𝟙 _
| _ _ arr := f

def walking_arrow.morphism_to_functor {C : Type*} [category C] {x y : C} (f : x ⟶ y)
  : walking_arrow ⥤ C := {
    obj := walking_arrow.morphism_to_functor_obj f,
    map := λ _ _, walking_arrow.morphism_to_functor_map f,
    map_comp' := by { intros X Y Z f g, cases f; cases g; symmetry;
                      dsimp [walking_arrow.comp, walking_arrow.morphism_to_functor_map];
                      try { exact category.id_comp' _ }; try { exact category.comp_id' _ }, }
  }

def walking_arrow.commutative_square_to_nat_trans_app {C : Type*} [category C] {x y x' y' : C}
  (f : x ⟶ y) (g : x' ⟶ y') 
  (u : x ⟶ x') (v : y ⟶ y') (w : u ≫ g = f ≫ v)
  : Π (i : walking_arrow), (walking_arrow.morphism_to_functor f).obj i
                         ⟶ (walking_arrow.morphism_to_functor g).obj i
| source := u
| target := v

def arrow_category_iso_functor_category (C : Type*) [category C]
  : Cat.of (arrow C) ≅ Cat.of (walking_arrow ⥤ C) := {
  hom := {
    obj := λ f, walking_arrow.morphism_to_functor f.hom,
    map := λ f g w, {
      app := walking_arrow.commutative_square_to_nat_trans_app f.hom g.hom _ _ w.w,
      naturality' := by { intros i j a, cases a,
                          { delta walking_arrow.morphism_to_functor, unfold_projs,
                            simp [walking_arrow.morphism_to_functor_map] },
                          { symmetry, exact w.w } }
    },
    map_id' := by { intro X, ext i, cases i; refl },
    map_comp' := by { intros X Y Z f g, ext i, cases i; refl }
  },
  inv := {
    obj := λ f, arrow.mk (f.map walking_arrow_hom.arr),
    map := λ f g η, arrow.hom_mk (η.naturality walking_arrow_hom.arr).symm
  },
  hom_inv_id' := by { apply functor.hext,
                      { rintro ⟨_, _, f⟩, refl },
                      { rintros ⟨_, _, f⟩ ⟨_, _, g⟩ ⟨u, v, w⟩, refl } },
  inv_hom_id' := by { apply category_theory.functor.ext, swap,
                      { rintro ⟨f_obj, f_map, hf1, hf2⟩, apply functor.hext,
                        { intro i, cases i; refl },
                        { intros i j a, cases a,
                          { refine heq_of_eq_of_heq (category_theory.functor.map_id _ i)
                                    (heq_of_heq_of_eq _ (category_theory.functor.map_id _ i).symm), 
                            congr' 1, cases i; refl },
                          { refl } } },
                      { rintro ⟨f_obj, f_map, hf1, hf2⟩ ⟨g_obj, g_map, hg1, hg2⟩ ⟨η, hη⟩,
                        rw Cat.comp_map, dsimp,
                        ext i, cases i; rw Cat.id_map;
                        repeat { rw nat_trans.comp_app };
                        rw [eq_to_hom_app, eq_to_hom_app, eq_to_hom_refl, eq_to_hom_refl,
                            category.id_comp, category.comp_id]; refl } }
}.

instance arrow_has_finite_limits {C : Type*} [category C] [limits.has_finite_limits C]
  : limits.has_finite_limits (arrow C) :=
  ⟨λ J i1 i2,  @adjunction.has_limits_of_shape_of_equivalence (walking_arrow ⥤ C) _ (arrow C) _ J i1
                                                              (category_theory.iso_to_equiv (arrow_category_iso_functor_category C)).functor
                                                              _
                                                              (@limits.has_finite_limits.out _ _ limits.functor_category_has_finite_limits J i1 i2)⟩.


instance {A : Type*} [category A] [preadditive A] {B : Type*} [category B] [preadditive B]
         {T : Type*} [category T] [preadditive T]
         {L : A ⥤ T} [L.additive] {R : B ⥤ T} [R.additive]
         (X Y : comma L R) : add_comm_group (comma_morphism X Y) := {
    add := λ w v, ⟨w.left + v.left, w.right + v.right, by simp⟩,
    zero := ⟨0, 0, by simp⟩,
    neg := λ w, ⟨-w.left, -w.right, by simp⟩,
    add_assoc := by { rintros ⟨wl, wr, hw⟩ ⟨vl, vr, hv⟩ ⟨ul, ur, hu⟩, apply comma_morphism.ext,
                      { exact add_assoc wl vl ul }, { exact add_assoc wr vr ur } },
    zero_add := by { rintro ⟨wl, wr, hw⟩, apply comma_morphism.ext,
                     { exact zero_add wl }, { exact zero_add wr } },
    add_zero := by { rintro ⟨wl, wr, hw⟩, apply comma_morphism.ext,
                     { exact add_zero wl }, { exact add_zero wr } },
    add_left_neg := by { rintro ⟨wl, wr, hw⟩, apply comma_morphism.ext,
                         { exact add_left_neg wl }, { exact add_left_neg wr } },
    add_comm := by { rintros ⟨wl, wr, hw⟩ ⟨vl, vr, hv⟩, apply comma_morphism.ext,
                     { exact add_comm wl vl }, { exact add_comm wr vr } }
  }.

@[simp] 
lemma comma.add_left_eq {A : Type*} [category A] [preadditive A]
                        {B : Type*} [category B] [preadditive B]
                        {T : Type*} [category T] [preadditive T]
                        {L : A ⥤ T} [L.additive] {R : B ⥤ T} [R.additive] 
                        {P Q : comma L R} (f g : P ⟶ Q) 
                       : (f + g).left = f.left + g.left := rfl

@[simp] 
lemma comma.add_right_eq {A : Type*} [category A] [preadditive A]
                         {B : Type*} [category B] [preadditive B]
                         {T : Type*} [category T] [preadditive T]
                         {L : A ⥤ T} [L.additive] {R : B ⥤ T} [R.additive] 
                         {P Q : comma L R} (f g : P ⟶ Q) 
                        : (f + g).right = f.right + g.right := rfl

instance {A : Type*} [category A] [preadditive A] {B : Type*} [category B] [preadditive B]
         {T : Type*} [category T] [preadditive T]
         {L : A ⥤ T} [L.additive] {R : B ⥤ T} [R.additive] 
         : preadditive (comma L R) := {}.

instance arrow_preadditive {V : Type*} [category V] [preadditive V] : preadditive (arrow V) :=
category_theory.comma.category_theory.preadditive.

instance arrow_iso_functor_preserves_zero {V : Type*} [category V] [preadditive V]
  : @functor.preserves_zero_morphisms (arrow V) _ (walking_arrow ⥤ V) _
                                      (@preadditive.preadditive_has_zero_morphisms _ _ arrow_preadditive) _
                                      (arrow_category_iso_functor_category V).hom :=
  ⟨by { intros f g, ext i, cases i; refl }⟩

noncomputable
instance arr_ab {V : Type*} [category V] [abelian V] : abelian (arrow V) := 
  @abelian_of_equivalence _ _ arrow_preadditive _ 
                          (walking_arrow ⥤ V) _ _ 
                          (category_theory.iso_to_equiv (arrow_category_iso_functor_category V)).functor
                          arrow_iso_functor_preserves_zero _.

universes v' v u'' u' u
open category_theory.limits

def mk_arrow_diagram {C : Type u} [category.{v} C] 
  {J : Type*} [category J] {K1 K2 : J ⥤ C} (η : K1 ⟶ K2)
  : J ⥤ arrow C := {
    obj := λ j, arrow.mk (η.app j),
    map := λ i j f, arrow.hom_mk' (η.naturality f)
  }.

def mk_arrow_cocone {C : Type u} [category.{v} C] 
  {J : Type*} [category J] (K1 K2 : J ⥤ C) (η : K1 ⟶ K2)
  {c1 : cocone K1} (hc1 : is_colimit c1) (c2 : cocone K2)
  : cocone (mk_arrow_diagram η) := {
    X := hc1.desc ((cocones.precompose η).obj c2),
    ι := { app := λ j, arrow.hom_mk' (eq.trans (hc1.fac _ j) (congr_fun (congr_arg _ (cocones.precompose_obj_ι η c2)) j)),
           naturality' := by { intros, ext; dsimp [mk_arrow_diagram]; simp } }
  }.

noncomputable
def preserves_colim_into_arrow_category {C : Type u} [category.{(max u'' v)} C] 
  {D : Type u'} [category.{v'} D] (F : arrow C ⥤ D)
  {J : Type u''} [small_category J] {K : J ⥤ arrow C}
  [has_colimits C]
  (H : ∀ {c1 : cocone (K ⋙ arrow.left_func)} (hc1 : is_colimit c1)
         {c2 : cocone (K ⋙ arrow.right_func)} (hc2 : is_colimit c2),
         is_colimit (F.map_cocone (mk_arrow_cocone (K ⋙ arrow.left_func) (K ⋙ arrow.right_func)
                                                   (whisker_left K arrow.left_to_right) hc1 c2)))
  : preserves_colimit K F :=
begin
  let e := category_theory.iso_to_equiv (arrow_category_iso_functor_category C),
  refine category_theory.limits.preserves_colimits_of_equiv_domain _ e _,
  constructor, intros c hc,
  let h := λ k,
          @preserves_colimits_of_shape.preserves_colimit _ _ _ _ _ _ _
            (@preserves_colimits_of_size.preserves_colimits_of_shape _ _ _ _ _
              (@limits.preserves_colimits_of_size_shrink _ _ _ _ _
                (@limits.evaluation_preserves_colimits C _ walking_arrow _ _ k)) J _)
            (K ⋙ e.functor),
  let hSource := @limits.is_colimit_of_preserves _ _ _ _ _ _ _ _ _ hc (h walking_arrow.source),
  let hTarget := @limits.is_colimit_of_preserves _ _ _ _ _ _ _ _ _ hc (h walking_arrow.target),
  refine is_colimit.of_iso_colimit _ (functor.map_cocone_comp' (K ⋙ e.functor) e.inverse F c).symm,
  convert H hSource hTarget,
  dsimp [mk_arrow_cocone, mk_arrow_diagram, functor.map_cocone,
          cocones.functoriality, cocones.precompose],
  have : ∀ h, c.X.map arr
            = hSource.desc { X := c.X.obj target,
                             ι := @whisker_left J _ (arrow C) _ C _ K _ _ arrow.left_to_right
                                  ≫ { app := λ (j : J), (c.ι.app j).app target,
                                      naturality' := h }},
  { intro h, refine hSource.hom_ext _, intro j,
    rw hSource.fac,
    symmetry,
    simp,
    refine eq.trans _ ((c.ι.app j).naturality arr),
    refl },
  congr,
  { dsimp [e, category_theory.iso_to_equiv, arrow_category_iso_functor_category],
    congr,
    apply this },
  { dsimp [e, category_theory.iso_to_equiv, arrow_category_iso_functor_category,
           functor.associator, category_struct.comp, nat_trans.vcomp],
    congr,
    { apply this },
    { ext, refl, intros j j' h, cases h, rw category.id_comp _, congr,
      { apply this },
      { apply this },
      { apply proof_irrel_heq } },
    { apply proof_irrel_heq } }
end.
