import category_theory.arrow category_theory.category.Cat category_theory.abelian.transfer
import category_theory.limits.shapes.functor_category category_theory.limits.preserves.shapes.zero
import category_theory.abelian.functor_category
import algebra.homology.homology

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

def arrow_category_iso_functor_category {C : Type*} [category C]
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
  ⟨λ J i1 i2, @adjunction.has_limits_of_shape_of_equivalence (walking_arrow ⥤ C) _ (arrow C) _ J i1
                                                             arrow_category_iso_functor_category.hom
                                                             ⟨arrow_category_iso_functor_category.inv,
                                                              eq_to_iso (eq.symm (arrow_category_iso_functor_category.hom_inv_id)),
                                                              eq_to_iso (arrow_category_iso_functor_category.inv_hom_id),
                                                              by { intro, cases X, simp, refl }⟩
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
                                      arrow_category_iso_functor_category.hom :=
  ⟨by { intros f g, ext i, cases i; refl }⟩

noncomputable
instance arr_ab {V : Type*} [category V] [abelian V] : abelian (arrow V) := 
  @abelian_of_equivalence _ _ arrow_preadditive _ 
                          (walking_arrow ⥤ V) _ _ 
                          arrow_category_iso_functor_category.hom
                          arrow_iso_functor_preserves_zero
                          ⟨arrow_category_iso_functor_category.inv,
                           eq_to_iso (eq.symm (arrow_category_iso_functor_category.hom_inv_id)),
                           eq_to_iso (arrow_category_iso_functor_category.inv_hom_id),
                           by { intro, cases X, simp, refl }⟩