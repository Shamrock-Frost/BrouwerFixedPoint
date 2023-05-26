import category_theory.arrow category_theory.category.Cat category_theory.abelian.transfer
import category_theory.limits.shapes.functor_category category_theory.limits.preserves.shapes.zero
import category_theory.abelian.functor_category category_theory.preadditive.additive_functor
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
    map_comp' := by {
      intros X Y Z f g, cases f; cases g; symmetry;
      dsimp only [walking_arrow.morphism_to_functor_map];
      try { exact category.id_comp' _ }; try { exact category.comp_id' _ }
    }
  }

def walking_arrow.commutative_square_to_nat_trans_app {C : Type*} [category C] {x y x' y' : C}
  (f : x ⟶ y) (g : x' ⟶ y') 
  (u : x ⟶ x') (v : y ⟶ y') (w : u ≫ g = f ≫ v)
  : Π (i : walking_arrow), (walking_arrow.morphism_to_functor f).obj i
                         ⟶ (walking_arrow.morphism_to_functor g).obj i
| source := u
| target := v

-- we actually have a strict isomorphism of categories, is this all worth it?
def arrow.to_walking_arrow_functor (C : Type*) [category C]
  : arrow C ⥤ (walking_arrow ⥤ C) := {
    obj := λ f, walking_arrow.morphism_to_functor f.hom,
    map := λ f g w, {
      app := walking_arrow.commutative_square_to_nat_trans_app f.hom g.hom _ _ w.w,
      naturality' := by {
        intros i j a, cases a,
        { delta walking_arrow.morphism_to_functor, unfold_projs,
          simp only [walking_arrow.morphism_to_functor_map,
                     category.id_comp, category.comp_id] },
        { symmetry, exact w.w }
      }
    },
    map_id' := by { intro X, ext i, cases i; refl },
    map_comp' := by { intros X Y Z f g, ext i, cases i; refl }
  }

def walking_arrow_functor.to_arrow (C : Type*) [category C]
  : (walking_arrow ⥤ C) ⥤ arrow C := {
    obj := λ f, arrow.mk (f.map walking_arrow_hom.arr),
    map := λ f g η, arrow.hom_mk (η.naturality walking_arrow_hom.arr).symm
  }

def arrow.ident_iso_to_walking_to_arrow (C : Type*) [category C]
  :  𝟭 (arrow C) ≅ arrow.to_walking_arrow_functor C ⋙ walking_arrow_functor.to_arrow C := {
    hom := {
      app := λ X, match X with ⟨l, r, f⟩ := 𝟙 (arrow.mk f) end,
      naturality' := by {
        rintros ⟨l, r, f⟩ ⟨l', r', g⟩ ⟨ϕ, ψ, w⟩,
        ext,
        { rw [functor.id_map, comma.comp_left, functor.comp_map],
          dsimp only [arrow.ident_iso_to_walking_to_arrow._match_1],
          refine eq.trans (congr_arg2 _ rfl comma.id_left) _,
          rw [category.comp_id],
          refine eq.trans (category.id_comp _).symm _,
          exact congr_arg2 _ (eq.symm comma.id_left) rfl },
        { rw [functor.id_map, comma.comp_right, functor.comp_map],
          dsimp only [arrow.ident_iso_to_walking_to_arrow._match_1],
          refine eq.trans (congr_arg2 _ rfl comma.id_right) _,
          rw [category.comp_id],
          refine eq.trans (category.id_comp _).symm _,
          exact congr_arg2 _ (eq.symm comma.id_right) rfl }
      }
    },
    inv := {
      app := λ X, match X with ⟨l, r, f⟩ := 𝟙 (arrow.mk f) end,
      naturality' := by {
        rintros ⟨l, r, f⟩ ⟨l', r', g⟩ ⟨ϕ, ψ, w⟩,
        ext,
        { rw [functor.id_map, comma.comp_left, functor.comp_map],
          dsimp only [arrow.ident_iso_to_walking_to_arrow._match_2],
          refine eq.trans (congr_arg2 _ rfl comma.id_left) _,
          rw [category.comp_id],
          refine eq.trans (category.id_comp _).symm _,
          exact congr_arg2 _ (eq.symm comma.id_left) rfl },
        { rw [functor.id_map, comma.comp_right, functor.comp_map],
          dsimp only [arrow.ident_iso_to_walking_to_arrow._match_2],
          refine eq.trans (congr_arg2 _ rfl comma.id_right) _,
          rw [category.comp_id],
          refine eq.trans (category.id_comp _).symm _,
          exact congr_arg2 _ (eq.symm comma.id_right) rfl }
      }
    },
    hom_inv_id' := by {
      ext x; cases x with l r f,
      { simp only [nat_trans.comp_app, nat_trans.id_app, arrow.id_left,
                   arrow.ident_iso_to_walking_to_arrow._match_1, 
                   arrow.ident_iso_to_walking_to_arrow._match_2],
        rw category.id_comp (𝟙 (arrow.mk f)),
        exact comma.id_left },
      { simp only [nat_trans.comp_app, nat_trans.id_app, arrow.id_right,
                   arrow.ident_iso_to_walking_to_arrow._match_1, 
                   arrow.ident_iso_to_walking_to_arrow._match_2],
        rw category.id_comp (𝟙 (arrow.mk f)),
        exact comma.id_right }
    },
    inv_hom_id' := by {
      ext x; cases x with l r f,
      { simp only [nat_trans.comp_app, nat_trans.id_app, arrow.id_left,
                   arrow.ident_iso_to_walking_to_arrow._match_1, 
                   arrow.ident_iso_to_walking_to_arrow._match_2],
        rw category.id_comp (𝟙 (arrow.mk f)),
        exact comma.id_left },
      { simp only [nat_trans.comp_app, nat_trans.id_app, arrow.id_right,
                   arrow.ident_iso_to_walking_to_arrow._match_1, 
                   arrow.ident_iso_to_walking_to_arrow._match_2],
        rw category.id_comp (𝟙 (arrow.mk f)),
        exact comma.id_right }
    }
  }.

def walking_arrow_functor.to_arrow_to_walking_iso_ident (C : Type*) [category C]
  : walking_arrow_functor.to_arrow C ⋙ arrow.to_walking_arrow_functor C
  ≅ 𝟭 (walking_arrow ⥤ C) := {
    hom := {
      app := λ F, {
        app := λ X, match X with 
                    | source := 𝟙 (F.obj source)
                    | target := 𝟙 (F.obj target)
                    end,
        naturality' := by { intros X Y f, cases f,
                            { cases X;
                              refine eq.trans (category.id_comp _)
                                              (eq.trans (eq.symm (F.map_id _))
                                                        (category.id_comp _).symm) },
                            { exact eq.trans (category.comp_id _) (category.id_comp _).symm } }
      },
      naturality' := by {
        intros F G η,
        ext x, cases x;
        exact eq.trans (category.comp_id _) (category.id_comp _).symm
      }
    },
    inv := {
      app := λ F, {
        app := λ X, match X with 
                    | source := 𝟙 (F.obj source)
                    | target := 𝟙 (F.obj target)
                    end,
        naturality' := by { intros X Y f, cases f,
                            { cases X;
                              refine eq.trans (category.comp_id _)
                                              (eq.trans (F.map_id _)
                                                        (category.comp_id _).symm) },
                            { exact eq.trans (category.comp_id _) (category.id_comp _).symm } }
      },
      naturality' := by {
        intros F G η,
        ext x, cases x;
        exact eq.trans (category.comp_id _) (category.id_comp _).symm
      }
    },
    hom_inv_id' := by { ext F j, cases j; exact category.id_comp _ },
    inv_hom_id' := by { ext F j, cases j; exact category.id_comp _ }
  }

def arrow_category_equiv_functor_category (C : Type*) [category C]
  : arrow C ≌ (walking_arrow ⥤ C) := {
  functor := arrow.to_walking_arrow_functor C,
  inverse := walking_arrow_functor.to_arrow C,
  unit_iso := arrow.ident_iso_to_walking_to_arrow C,
  counit_iso := walking_arrow_functor.to_arrow_to_walking_iso_ident C,
  functor_unit_iso_comp' := by {
    rintro ⟨l, r, f⟩, ext j, cases j; exact category.comp_id _, 
  }
}.

instance arrow_has_finite_limits {C : Type*} [category C] [limits.has_finite_limits C]
  : limits.has_finite_limits (arrow C) :=
  ⟨λ J i1 i2,  @adjunction.has_limits_of_shape_of_equivalence (walking_arrow ⥤ C) _ (arrow C) _ J i1
                                                              (arrow_category_equiv_functor_category C).functor
                                                              _
                                                              (@limits.has_finite_limits.out _ _ limits.functor_category_has_finite_limits J i1 i2)⟩.


instance {A : Type*} [category A] [preadditive A] {B : Type*} [category B] [preadditive B]
         {T : Type*} [category T] [preadditive T]
         {L : A ⥤ T} [L.additive] {R : B ⥤ T} [R.additive]
         (X Y : comma L R) : add_comm_group (comma_morphism X Y) := {
    add := λ w v, ⟨w.left + v.left, w.right + v.right, 
      by simp only [functor.map_add, preadditive.add_comp, comma_morphism.w,
                    preadditive.comp_add, auto_param_eq]⟩,
    zero := ⟨0, 0, by simp only [functor.map_zero, auto_param_eq,
                                limits.comp_zero, limits.zero_comp]⟩,
    neg := λ w, ⟨-w.left, -w.right,
      by simp only [functor.map_neg, preadditive.neg_comp, comma_morphism.w,
                    preadditive.comp_neg, auto_param_eq]⟩,
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
                                      (arrow_category_equiv_functor_category V).functor :=
  ⟨by { intros f g, ext i, cases i; refl }⟩

noncomputable
instance arr_ab {V : Type*} [category V] [abelian V] : abelian (arrow V) := 
  @abelian_of_equivalence _ _ arrow_preadditive _ 
                          (walking_arrow ⥤ V) _ _ 
                          (arrow_category_equiv_functor_category V).functor
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
    ι := {
      app := λ j, arrow.hom_mk' (eq.trans (hc1.fac _ j) (congr_fun (congr_arg _ (cocones.precompose_obj_ι η c2)) j)),
      naturality' := by {
        intros,  ext;
        dsimp [is_colimit.fac, cocones.precompose_obj_ι, mk_arrow_diagram];
        simp only [cocone.w, category.comp_id]
      }
    }
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
  let e := arrow_category_equiv_functor_category C,
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
  dsimp only [mk_arrow_cocone, mk_arrow_diagram, functor.map_cocone,
              cocones.functoriality, cocones.precompose],
  have : ∀ h, c.X.map arr
            = hSource.desc { X := c.X.obj target,
                             ι := @whisker_left J _ (arrow C) _ C _ K _ _ arrow.left_to_right
                                  ≫ { app := λ (j : J), (c.ι.app j).app target,
                                      naturality' := h }},
  { intro h, refine hSource.hom_ext _, intro j,
    rw hSource.fac,
    symmetry,
    simp only [nat_trans.comp_app, whisker_left_app, arrow.left_to_right_app,
               functor.map_cocone_ι_app, evaluation_obj_map],
    refine eq.trans _ ((c.ι.app j).naturality arr),
    refl },
  congr,
  { dsimp only [e, arrow_category_equiv_functor_category,
                walking_arrow_functor.to_arrow],
    congr,
    apply this },
  { dsimp only [e, arrow_category_equiv_functor_category, nat_trans.vcomp, 
                walking_arrow_functor.to_arrow, functor.associator,
                category_struct.comp, nat_trans.naturality],
    congr,
    { apply this },
    { ext, refl, intros j j' h, cases h, rw category.id_comp _, congr,
      { apply this },
      { apply this },
      { apply proof_irrel_heq } },
    { apply proof_irrel_heq } }
end.
