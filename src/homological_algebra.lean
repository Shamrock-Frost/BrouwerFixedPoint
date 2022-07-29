import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import algebra.homology.quasi_iso
import category_theory.preadditive.left_exact
import category_theory.abelian.functor_category
import category_theory.limits.shapes.comm_sq
import data.list.tfae

import for_mathlib.homological_complex_abelian
import for_mathlib.les_homology
import for_mathlib.preserves_exact
import for_mathlib.snake_lemma_naturality2

import .category_theory .linear_algebra .arrow_category

open category_theory category_theory.limits homological_complex

local attribute [instance] category_theory.limits.has_zero_object.has_zero
local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

noncomputable
def coker_functor (V : Type*) [category V] [has_zero_morphisms V] [has_cokernels V]
  : arrow V ⥤ V := {
    obj := λ f, cokernel f.hom,
    map := λ f g φ, cokernel.map _ _ _ _ φ.w.symm,
    map_id' := by { intro, ext, simp, apply category.id_comp },
    map_comp' := by { intros, ext, simp }
  }

lemma coker_map_spec {V : Type*} [category V] [has_zero_morphisms V] [has_cokernels V]
  {A B X Y : V}
  (i : A ⟶ X) (j : B ⟶ Y)
  (f' : A ⟶ B) (f : X ⟶ Y)
  (w1 : i ≫ f = f' ≫ j)
  : cokernel.π i ≫ cokernel.map i j f' f w1 = f ≫ cokernel.π j :=
  by { delta cokernel.π coequalizer.π cokernel.map, simp }

noncomputable
def coker_functor_proj (V : Type*) [category V] [has_zero_morphisms V] [has_cokernels V]
  : arrow.right_func ⟶ coker_functor V := {
    app := λ f, cokernel.π f.hom,
    naturality' := λ f g ϕ, by { change ϕ.right ≫ cokernel.π g.hom
                                      = cokernel.π f.hom ≫ cokernel.map _ _ _ _ ϕ.w.symm,
                                 rw coker_map_spec,
                                 refl }
  }

-- Why can't lean synthesize the arrow_preadditive instance?
instance coker_additive {V : Type*} [category V] [preadditive V] [has_cokernels V]
  : @functor.additive _ _ _ _ arrow_preadditive _ (coker_functor V) :=
  ⟨by { rintros ⟨f⟩ ⟨g⟩ ⟨αl, αr⟩ ⟨βl, βr⟩, dsimp [coker_functor], ext, simp }⟩.

-- lemma coker_right_exact {V : Type*} [category V] [abelian V]
--   {f g h : arrow V} (α : f ⟶ g) (β : g ⟶ h)
--   (h : @short_exact _ _ _ _ _ α β
--                     (@preadditive.preadditive_has_zero_morphisms _ _ arr_ab.to_preadditive)
--                     arr_ab.has_kernels
--                     (@abelian.of_coimage_image_comparison_is_iso.has_images _ _
--                                                                             arr_ab.to_preadditive
--                                                                             arr_ab.has_kernels
--                                                                             arr_ab.has_cokernels
--                                                                             (@abelian.coimage_image_comparison.category_theory.is_iso _ _ arr_ab)))
--   : exact ((coker_functor V).map f) (F.map g) ∧ epi (F.map g)

section snake_diagram 

open category_theory.snake_diagram

local notation x `⟶[`D`]` y := D.map (hom x y)

lemma to_zero_exact_of_epi {V : Type*} [category V] [abelian V] {X Y : V} (Z : V) (f : X ⟶ Y)
  : epi f → exact f (0 : Y ⟶ Z) := ((abelian.tfae_epi Z f).out 0 2).mp

def cokernel_sequence
  {V : Type*} [category V] [abelian V]
  (D : snake_input V)
  (h1 : epi ((2, 1) ⟶[D] (2, 2)))
  : exact_seq V [((3, 0) ⟶[D] (3, 1)), ((3, 1) ⟶[D] (3, 2)), (0 : D.obj (3, 2) ⟶ 0)] :=
  have h2 : exact ((3, 0) ⟶[D] (3, 1)) ((3, 1) ⟶[D] (3, 2)) := D.2.row_exact _,
  have h3 : epi ((3, 1) ⟶[D] (3, 2)),
  begin
    letI := h1,
    refine abelian.pseudoelement.epi_of_pseudo_surjective _ (λ y, _),
    refine is_snake_input.exists_of_exact (is_snake_input.long_row₃_exact D.is_snake_input) y _,
    simp [is_snake_input.bottom_right_to_coker_row₂,
          limits.cokernel.π_of_epi ((2, 1) ⟶[D] (2, 2))]
  end,
  exact_seq.cons _ _ h2 _
    (exact_seq.cons _ _ (to_zero_exact_of_epi _ _ h3) _
      (exact_seq.single _))

end snake_diagram

lemma coker_right_exact {V : Type*} [category V] [abelian V]
  {A B C X Y Z : V}
  (f : A ⟶ B) (g : B ⟶ C) (f' : X ⟶ Y) (g' : Y ⟶ Z)
  (α : A ⟶ X) (β : B ⟶ Y) (γ : C ⟶ Z)
  (w1 : f ≫ β = α ≫ f') (w2 : g ≫ γ = β ≫ g')
  (H : short_exact f g) (H' : short_exact f' g')
  : exact_seq V [((coker_functor V).map (arrow.hom_mk w1 : arrow.mk α ⟶ arrow.mk β)),
                 ((coker_functor V).map (arrow.hom_mk w2 : arrow.mk β ⟶ arrow.mk γ)),
                 (0 : cokernel γ ⟶ 0)] :=
begin
  letI := H.mono, letI := H.epi, letI := H'.mono, letI := H'.epi, 
  convert cokernel_sequence (snake.mk_of_sequence_hom A B C X Y Z f g α β γ f' g'
                                                      w1.symm w2.symm H.exact H'.exact).snake_input _;
  dsimp [coker_functor, snake.snake_input, snake.snake_diagram, snake_diagram.mk_functor,
         snake_diagram.mk_functor.map'];
  simp only [category_theory.functor.map_id, category.id_comp, category.comp_id],
  { refl }, { refl },
  { exact H'.epi }
end

lemma right_exact_of_sends_SES_to_right_exact 
  {V W : Type*} [category V] [category W] [abelian V] [abelian W]
  (F : V ⥤ W) [F.additive]
  (hF : ∀ {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [mono f] [epi g],
          exact f g → exact (F.map f) (F.map g) ∧ epi (F.map g))
  {X Y Z} (f : X ⟶ Y) (g : Y ⟶ Z) [epi g] (H : exact f g)
  : exact (F.map f) (F.map g) ∧ epi (F.map g) :=
  have preserves_epi : ∀ {P Q} (s : P ⟶ Q) [epi s], epi (F.map s) :=
    λ P Q s hs, (@hF _ _ _ (kernel.ι s) s _ hs (snake_diagram.exact_kernel_ι_self s)).right,
  have H' : image.ι f ≫ g = 0,
  by { apply (factor_thru_image.category_theory.epi f).left_cancellation, simp, exact H.w },
  have H'' : exact (image.ι f) g,
  from ⟨H', by { have h1 := H.epi,
                rw ← subobject_of_le_as_image_to_kernel _ _ H.w (image_le_kernel _ _ H.w) at h1,
                rw ← subobject_of_le_as_image_to_kernel _ _ H' (image_le_kernel _ _ H'),
                have h2 : image_subobject f ≤ image_subobject (image.ι f),
                { transitivity image_subobject (factor_thru_image f ≫ image.ι f),
                  { apply le_of_eq, symmetry, congr, apply image.fac },
                  { apply image_subobject_comp_le } },
                rw ← category_theory.subobject.of_le_comp_of_le _ _ _ h2 (image_le_kernel _ _ H') at h1,
                refine @epi_of_epi _ _ _ _ _ _ _ h1 }⟩,
  by { have := hF (image.ι f) g H'', refine ⟨_, this.right⟩,
        rw ← image.fac f,
        rw F.map_comp,
        refine (@abelian.exact_epi_comp_iff _ _ _ _ _ _ _ _ _ _
                                            (preserves_epi (factor_thru_image f))).mpr this.left }

lemma any_coker_of_isos_is_iso {V : Type*} [category V] [abelian V]
  {A B C X Y Z : V} (f : A ⟶ B) (g : B ⟶ C) (f' : X ⟶ Y) (g' : Y ⟶ Z)
  (α : A ⟶ X) (β : B ⟶ Y) (γ : C ⟶ Z)
  (h1 : exact_seq V [f, g, (0 : C ⟶ 0)]) (h2 : exact_seq V [f', g', (0 : Z ⟶ 0)])
  (sq1 : α ≫ f' = f ≫ β) (sq2 : β ≫ g' = g ≫ γ)
  (hα : is_iso α) (hβ : is_iso β) : is_iso γ :=
begin
  -- One can do this very concretely but I don't want to l m a o
  have sq3 : γ ≫ (0 : _ ⟶ 0) = (0 : _ ⟶ 0) ≫ (0 : 0 ⟶ 0), { simp },
  have sq4 : (0 : (0 : V) ⟶ 0) ≫ (0 : 0 ⟶ 0) = (0 : 0 ⟶ 0) ≫ 0 := rfl,
  refine abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso sq1 sq2 sq3 sq4 _ _ _ _ _ _,
  { exact (exact_iff_exact_seq _ _).mpr (h1.extract 0 2) },
  { exact (exact_iff_exact_seq _ _).mpr (h1.extract 1 3) },
  { apply to_zero_exact_of_epi, apply_instance },
  { exact (exact_iff_exact_seq _ _).mpr (h2.extract 0 2) },
  { exact (exact_iff_exact_seq _ _).mpr (h2.extract 1 3) },
  { apply to_zero_exact_of_epi, apply_instance }
end

lemma coker_of_mono_bicartesian_square_is_iso {V : Type*} [category V] [abelian V] {X A B Y  : V}
  (i : X ⟶ A)  (j : X ⟶ B)  (k : A ⟶ Y)  (ℓ : B ⟶ Y)
  (hi : mono i) (hj : mono j) (hk : mono k) (hℓ : mono ℓ)
  (h1 : is_pullback i j k ℓ) (h1 : is_pushout i j k ℓ)
  : is_iso ((coker_functor V).map (arrow.hom_mk h1.to_comm_sq.w.symm
                                  : arrow.mk i ⟶ arrow.mk ℓ)) :=
begin
  admit
end

section general_abelian_category

universes u u' v v'

parameters {C : Type u} {V : Type v} [category.{u'} C] [category.{v'} V]
parameters {ι : Type} {c : complex_shape ι}

lemma id_eq_zero_of_iso_zero [has_zero_object V] [has_zero_morphisms V] [has_cokernels V] (X : V)
  : is_isomorphic X 0 → 𝟙 X = 0
| ⟨H⟩ := calc 𝟙 X = H.hom ≫ H.inv : H.hom_inv_id.symm
             ... = H.hom ≫ 0     : congr_arg _ (has_zero_object.from_zero_ext H.inv 0)
             ... = 0              : comp_zero

lemma homology_at_ith_index_zero
  [has_zero_object V] [has_zero_morphisms V] [has_equalizers V] [has_cokernels V]
  [has_images V] [has_image_maps V]
  {X Y : homological_complex V c} (f : X ⟶ Y) (i : ι) (H : f.f i = 0)
  : (homology_functor V c i).map f = 0 :=
begin
  dsimp [homology_functor, homology.map],
  convert cokernel.desc_zero _,
  { convert zero_comp, dsimp [hom.sq_from, kernel_subobject_map], simp_rw [H, comp_zero],
    exact subobject.factor_thru_zero _ },
  exact comp_zero
end

def homological_complex_functor.mk_nat_trans [has_zero_morphisms V]
  {F G : C ⥤ homological_complex V c}
  (η : Π (i : ι), (F ⋙ homological_complex.eval V c i) ⟶ (G ⋙ homological_complex.eval V c i))
  (η_comm_ds : ∀ (i j : ι), c.rel i j →
                  ∀ X, (η i).app X ≫ (G.obj X).d i j = (F.obj X).d i j ≫ (η j).app X)
  : F ⟶ G := {
    app := λ X, { f := λ i, (η i).app X,
                  comm' := by exact λ i j h, η_comm_ds i j h X },
    naturality' := λ X Y f, homological_complex.hom.ext _ _ (funext (λ i, (η i).naturality f))
  }

def homological_complex.d_nat_trans [has_zero_morphisms V]
  (F : C ⥤ homological_complex V c) (i j : ι)
  : (F ⋙ homological_complex.eval V c i) ⟶ (F ⋙ homological_complex.eval V c j) := {
    app := λ X, (F.obj X).d i j,
    naturality' := by simp
  }

structure natural_chain_homotopy [preadditive V]
  {F G : C ⥤ homological_complex V c} (α β : nat_trans F G)
  : Type (max u (max v (v' + 1))) :=
(to_chain_htpy : ∀ X, @homotopy ι V _ _ c (F.obj X) (G.obj X) (α.app X) (β.app X))
(naturality : ∀ X Y (f : X ⟶ Y) i j, c.rel i j → (F.map f).f j ≫ (to_chain_htpy Y).hom j i
                                                = (to_chain_htpy X).hom j i ≫ (G.map f).f i)

-- This is why we run into universe issues and need ι : Type
-- parallel_pair_comp is an equality between two functors
-- and that constrains them to be in the same universe
protected def parallel_pair_comp_has_colim 
 [has_zero_morphisms V] [has_cokernels V]
  {X Y : homological_complex V c} (f : X ⟶ Y) (p : ι)
  : has_colimit (parallel_pair f 0 ⋙ eval V c p) := by {
    rw parallel_pair_comp, dsimp, apply_instance
  }

local attribute [instance] parallel_pair_comp_has_colim

noncomputable
def coker_of_chain_map_at [has_zero_morphisms V] [has_cokernels V]
  {X Y : homological_complex V c} (f : X ⟶ Y) (p : ι)
  : cocone (parallel_pair (f.f p) 0) :=
  parallel_pair_comp.cocone_comp_to_cocone_pair (eval V c p : homological_complex V c ⥤ V) f 0
                                                ((eval V c p).map_cocone
                                                  (colimit.cocone (parallel_pair f 0)))

noncomputable
def coker_of_chain_map_at_is_colimit [has_zero_morphisms V] [has_cokernels V]
  {X Y : homological_complex V c} (f : X ⟶ Y) (p : ι)
  : is_colimit (coker_of_chain_map_at f p) :=
    parallel_pair_comp.is_colimit_comp_to_is_colimit_pair _ _ _ _
      (is_colimit_of_preserves (eval V c p) (colimit.is_colimit (parallel_pair f 0)))

noncomputable
def chain_homotopy_on_coker_of_compatible_chain_homotopies
  [preadditive V] [has_cokernels V]
  {A B X Y : homological_complex V c}
  (i : A ⟶ X) (j : B ⟶ Y)
  (f' g' : A ⟶ B) (f g : X ⟶ Y)
  (w1 : f' ≫ j = i ≫ f) (w2 : g' ≫ j = i ≫ g)
  (s' : homotopy f' g') (s : homotopy f g)
  (comm : s'.comp_right j = (homotopy.of_eq w1).trans ((s.comp_left i).trans (homotopy.of_eq w2.symm)))
  : homotopy ((coker_functor (homological_complex V c)).map (arrow.hom_mk w1 : arrow.mk i ⟶ arrow.mk j))
             ((coker_functor (homological_complex V c)).map (arrow.hom_mk w2 : arrow.mk i ⟶ arrow.mk j)) := {
  hom := λ p q, is_colimit.desc
                  (coker_of_chain_map_at_is_colimit i p)
                  (cofork.of_π (s.hom p q ≫ cofork.π (coker_of_chain_map_at j q)) 
                  (by { rw [zero_comp, ← category.assoc],
                        have := congr_arg (λ h, homotopy.hom h p q) comm, simp at this,
                        rw [← this, category.assoc, cokernel_cofork.condition, comp_zero] })),
  zero' := by { intros p q h,
                have : i.f p ≫ 0 = 0 ≫ 0 := eq.trans comp_zero comp_zero.symm,
                transitivity (coker_of_chain_map_at_is_colimit i p).desc (cofork.of_π 0 this),
                { congr, rw s.zero' p q h, exact zero_comp },
                { symmetry,
                  refine (coker_of_chain_map_at_is_colimit i p).uniq' (cofork.of_π 0 this) 0 _,
                  intro u, cases u; simp } },
  comm := by { intro p,
               have H : ∀ (h' : A ⟶ B) (h : X ⟶ Y) (w : h' ≫ j = i ≫ h),
                        i.f p ≫ homological_complex.hom.f h p
                              ≫ cofork.π (coker_of_chain_map_at j p)
                      = 0 ≫ homological_complex.hom.f h p ≫ cofork.π (coker_of_chain_map_at j p),
               { intros h' h w, rw [zero_comp, ← category.assoc],
                 have := congr_arg (λ h, homological_complex.hom.f h p) w, dsimp at this,
                 rw [← this, category.assoc, cokernel_cofork.condition, comp_zero] },
               have : ∀ (h' : A ⟶ B) (h : X ⟶ Y) (w : h' ≫ j = i ≫ h),
                        ((coker_functor (homological_complex V c)).map
                          (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j)).f p
                      = is_colimit.desc
                          (coker_of_chain_map_at_is_colimit i p)
                          (cofork.of_π (h.f p ≫ cofork.π (coker_of_chain_map_at j p)) (H h' h w)),
               { intros h' h w,
                 apply (coker_of_chain_map_at_is_colimit i p).uniq'
                         (cofork.of_π (h.f p ≫ cofork.π (coker_of_chain_map_at j p)) (H h' h w)),
                 intro u, cases u; simp,
                 refine eq.trans (category.assoc _ _ _) _,
                 refine eq.trans _ (category.assoc _ _ _),
                 simp,
                 refine eq.trans (category.id_comp _) _,
                 refine eq.trans _ (congr_arg _ (category.id_comp _).symm),
                 change (cokernel.π i
                         ≫ (coker_functor (homological_complex V c)).map
                              (arrow.hom_mk w  : arrow.mk i ⟶ arrow.mk j)).f p
                        = (h ≫ cokernel.π j).f p,
                 congr' 1,
                 dsimp [coker_functor],
                 exact coker_map_spec i j h' h w.symm },
               rw [this f' f w1, this g' g w2],
               symmetry, apply is_colimit.uniq'
                                 (coker_of_chain_map_at_is_colimit i p)
                                 (cofork.of_π (f.f p ≫ cofork.π (coker_of_chain_map_at j p))
                                              (H f' f w1)),
               intro u, cases u; simp,
               have := congr_arg (λ t, t ≫ cofork.π (coker_of_chain_map_at j p)) (s.comm p),
               refine eq.trans _ this.symm,
               simp,
               delta cofork.π coker_of_chain_map_at parallel_pair_comp.cocone_comp_to_cocone_pair,
               dsimp,
               rw [category.assoc, ← d_next_comp_left, category.assoc, ← prev_d_comp_left], 
               apply congr_arg2; simp only [eq_to_hom_app, eq_to_hom_refl],
               { refine eq.trans (category.id_comp _) _,
                 refine eq.trans _ (congr_arg _ (category.id_comp _).symm),
                 rw ← d_next_comp_right, congr,
                 ext q r,
                 rw (_ : (cokernel.π i).f q
                       = cofork.π (coker_of_chain_map_at i q)),
                 simp,
                 exact congr_arg _ (category.id_comp _),
                 delta cofork.π coker_of_chain_map_at parallel_pair_comp.cocone_comp_to_cocone_pair,
                 simp, },
               { refine eq.trans (category.id_comp _) _,
                 refine eq.trans _ (congr_arg _ (category.id_comp _).symm),
                 rw ← prev_d_comp_right, congr,
                 ext q r,
                 rw (_ : (cokernel.π i).f q
                       = cofork.π (coker_of_chain_map_at i q)),
                 simp,
                 exact congr_arg _ (category.id_comp _),
                 delta cofork.π coker_of_chain_map_at parallel_pair_comp.cocone_comp_to_cocone_pair,
                 simp, } } }.

-- I should not have to do any of this...
noncomputable
instance [abelian V] (ℓ : ι) : preserves_finite_limits (eval V c ℓ) := 
begin
  constructor,
  intros J j1 j2,
  have : @has_limits_of_shape J j1 V _,
  { obtain ⟨H⟩ := @abelian.has_finite_limits V _ _,
    exact @H J j1 j2 },
  refine @eval.category_theory.limits.preserves_limits_of_shape V _ J j1 ι c _ this ℓ,
end

noncomputable
instance [abelian V] (ℓ : ι) : preserves_finite_colimits (eval V c ℓ) := 
begin
  constructor,
  intros J j1 j2,
  have : @has_colimits_of_shape J j1 V _,
  { obtain ⟨H⟩ := @abelian.has_finite_colimits V _ _,
    exact @H J j1 j2 },
  refine @eval.category_theory.limits.preserves_colimits_of_shape V _ J j1 ι c _ this ℓ,
end

def coker_functor_degreewise_SES [abelian V]
  {A X : homological_complex V c} (i : A ⟶ X) [mono i]
  : ∀ ℓ, short_exact (i.f ℓ)
                     (((coker_functor_proj (homological_complex V c)).app (arrow.mk i)).f ℓ) :=
begin
  intro,
  rw [ ← homological_complex.eval_map, ← homological_complex.eval_map],
  apply category_theory.functor.map_short_exact,
  dsimp [coker_functor_proj],
  refine short_exact.mk _,
  apply snake_diagram.exact_self_cokernel_π
end

lemma δ_natural' [abelian V]  
  {A B C X Y Z : homological_complex V c}
  (f : A ⟶ B) (g : B ⟶ C) (f' : X ⟶ Y) (g' : Y ⟶ Z)
  (α : A ⟶ X) (β : B ⟶ Y) (γ : C ⟶ Z)
  (H1 : ∀ p, short_exact (f.f p)  (g.f p))
  (H2 : ∀ p, short_exact (f'.f p) (g'.f p))
  (w1 : f ≫ β = α ≫ f') (w2 : g ≫ γ = β ≫ g') 
  (p q : ι) (hpq : c.rel p q) :
  δ f g H1 p q hpq ≫ (homology_functor _ _ q).map α =
    (homology_functor _ _ p).map γ ≫ δ f' g' H2 p q hpq :=
  let α' : walking_arrow ⥤ homological_complex V c :=
          arrow_category_iso_functor_category.hom.obj (arrow.mk α),
      β' : walking_arrow ⥤ homological_complex V c :=
          arrow_category_iso_functor_category.hom.obj (arrow.mk β),
      γ' : walking_arrow ⥤ homological_complex V c :=
          arrow_category_iso_functor_category.hom.obj (arrow.mk γ),
      F : α' ⟶ β' := arrow_category_iso_functor_category.hom.map (arrow.hom_mk w1),
      G : β' ⟶ γ' := arrow_category_iso_functor_category.hom.map (arrow.hom_mk w2) in
  have H : Π (x : walking_arrow) ℓ, short_exact ((F.app x).f ℓ) ((G.app x).f ℓ),
  by { intros, cases x, { exact H1 ℓ }, { exact H2 ℓ } },
  by { have := δ_natural F G H walking_arrow_hom.arr p q hpq, exact this }

noncomputable
def homology_iso_cokernel [abelian V] (ℓ : ι) (h : c.next ℓ = none) (A : homological_complex V c)
  : A.homology ℓ ≅ cokernel (A.d_to ℓ) :=
{ hom := homology.desc' _ _ _ (kernel.ι _ ≫ cokernel.π _) $ by simp,
  inv := cokernel.desc _ (homology.lift _ _ _ (cokernel.π _) $ by { simp, exact A.d_from_eq_zero h, })
  $ begin
    apply homology.hom_to_ext,
    simp,
  end,
  hom_inv_id' := begin
    apply homology.hom_from_ext,
    apply homology.hom_to_ext,
    simp,
  end,
  inv_hom_id' := begin
    apply coequalizer.hom_ext,
    simp,
    let t := _, change _ ≫ t = _,
    have ht : t = homology.ι _ _ _,
    { apply homology.hom_from_ext, simp, },
    simp [ht],
  end }

def homology_iso_cokernel_natural [abelian V] (ℓ : ι) (h : c.next ℓ = none)
  {A B : homological_complex V c} (f : A ⟶ B) :
  (homology_iso_cokernel ℓ h A).hom ≫ cokernel.map _ _ (f.prev _) (f.f _) (by simp) =
  (homology_functor _ _ _).map f ≫ (homology_iso_cokernel ℓ h B).hom :=
begin
  dsimp [homology_iso_cokernel],
  apply homology.hom_from_ext,
  simp,
end

lemma mono_prev [abelian V] (ℓ : ι) {A B : homological_complex V c} (f : A ⟶ B)
  (hf : ∀ m, mono (f.f m)) : mono (f.prev ℓ) :=
begin
  destruct (c.prev ℓ),
  { intro h, have : A.X_prev ℓ = 0, { delta homological_complex.X_prev, rw h },
    convert has_zero_object.category_theory.mono _,
    swap, { exact (has_zero_object.unique_to _).default },
    { apply heq_of_cast_eq _, swap, congr, exact this, apply (has_zero_object.unique_to _).uniq } },
  { rintros ⟨m, h⟩ _, rw hom.prev_eq _ h, apply_instance }
end

lemma short_exact_prev [abelian V] (ℓ : ι) {A B C : homological_complex V c}
  (f : A ⟶ B) (g : B ⟶ C) (h : ∀ m, short_exact (f.f m) (g.f m))
  : short_exact (f.prev ℓ) (g.prev ℓ) :=
  { mono := mono_prev ℓ f (λ m, (h m).mono),
    exact := exact_prev' _ _ ℓ (λ m, (h m).exact),
    epi := @homological_complex.epi_prev' _ _ _ _ _ _ _ _ _ (λ m, (h m).epi) }

-- shouldn't need abelian, but we need the category of homological complexes to have images
-- Suggests LTE has something messed up in its typeclasses
lemma terminal_homology_right_exact [abelian V] (ℓ : ι) (hℓ : c.next ℓ = none)
  {A B C : homological_complex V c}
  (f : A ⟶ B) (g : B ⟶ C) (h : ∀ m, short_exact (f.f m) (g.f m))
  : exact_seq V [(homology_functor V c ℓ).map f, (homology_functor V c ℓ).map g,
                 (0 : C.homology ℓ ⟶ 0)] :=
begin
  have := coker_right_exact (f.prev ℓ) (g.prev ℓ) (f.f ℓ) (g.f ℓ)
                            (A.d_to ℓ) (B.d_to ℓ) (C.d_to ℓ) (f.comm_to ℓ) (g.comm_to ℓ)
                            (short_exact_prev ℓ f g h) (h ℓ),
  constructor,
  { replace this := this.extract 0 2, dsimp [list.extract] at this,
    rw ← exact_iff_exact_seq at this,
    refine preadditive.exact_of_iso_of_exact' _ _ _ _ (homology_iso_cokernel ℓ hℓ A).symm
                                                      (homology_iso_cokernel ℓ hℓ B).symm
                                                      (homology_iso_cokernel ℓ hℓ C).symm _ _ this;
    { rw [iso.symm_hom, iso.symm_hom, iso.eq_comp_inv, category.assoc, iso.inv_comp_eq],
      symmetry, apply homology_iso_cokernel_natural } },
  { rw ← exact_iff_exact_seq,
    replace this := this.extract 1 3, dsimp [list.extract] at this,
    rw ← exact_iff_exact_seq at this,
    refine preadditive.exact_of_iso_of_exact' _ _ _ _ (homology_iso_cokernel ℓ hℓ B).symm
                                                      (homology_iso_cokernel ℓ hℓ C).symm
                                                      (iso.refl 0) _ _ this,
    { rw [iso.symm_hom, iso.symm_hom, iso.eq_comp_inv, category.assoc, iso.inv_comp_eq],
      symmetry, apply homology_iso_cokernel_natural },
    { simp } }
end

lemma coker_of_quasi_isos_between_monic_arrows_is_quasi_iso [abelian V]
  {A B X Y : homological_complex V c}
  (i : A ⟶ X) (j : B ⟶ Y)
  (hi : mono i) (hj : mono j)
  (g : A ⟶ B) (f : X ⟶ Y)
  (hg : quasi_iso g) (hf : quasi_iso f)
  (w : g ≫ j = i ≫ f)
  : quasi_iso ((coker_functor (homological_complex V c)).map (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j)) :=
begin
  constructor, intro ℓ,
  have sq1 := eq.trans (eq.symm ((homology_functor V c ℓ).map_comp' g j))
                       (eq.trans (congr_arg _ w) ((homology_functor V c ℓ).map_comp' i f)), 
  have sq2 : (homology_functor V c ℓ).map f
           ≫ (homology_functor V c ℓ).map ((coker_functor_proj (homological_complex V c)).app (arrow.mk j))
           = (homology_functor V c ℓ).map ((coker_functor_proj (homological_complex V c)).app (arrow.mk i))
           ≫ (homology_functor V c ℓ).map ((coker_functor _).map (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j)),
  { rw [← functor.map_comp, ← functor.map_comp], apply congr_arg,
    exact ((coker_functor_proj (homological_complex V c)).naturality' (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j)) },
  destruct (c.next ℓ),
  { intro h,
    have H := terminal_homology_right_exact ℓ h i
                ((coker_functor_proj (homological_complex V c)).app (arrow.mk i))
                (coker_functor_degreewise_SES i),
    have H' := terminal_homology_right_exact ℓ h j
                 ((coker_functor_proj (homological_complex V c)).app (arrow.mk j))
                 (coker_functor_degreewise_SES j),
    exact any_coker_of_isos_is_iso _ _ _ _
                                   ((homology_functor V c ℓ).map g)
                                   ((homology_functor V c ℓ).map f)
                                   ((homology_functor V c ℓ).map ((coker_functor _).map (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j)))
                                   H H' sq1 sq2 (quasi_iso.is_iso ℓ) (quasi_iso.is_iso ℓ) },
  { rintros ⟨m, hm⟩ _, 
    have sq3 := (δ_natural' i ((coker_functor_proj (homological_complex V c)).app (arrow.mk i))
                            j ((coker_functor_proj (homological_complex V c)).app (arrow.mk j))
                            g f
                            ((coker_functor _).map (arrow.hom_mk w : arrow.mk i ⟶ arrow.mk j))
                            (coker_functor_degreewise_SES i)
                            (coker_functor_degreewise_SES j) w.symm
                            ((coker_functor_proj (homological_complex V c)).naturality' _).symm
                            ℓ m hm).symm,
    have sq4 := eq.trans (eq.symm ((homology_functor V c m).map_comp' g j))
                         (eq.trans (congr_arg _ w) ((homology_functor V c m).map_comp' i f)),
    have LES1 := six_term_exact_seq i ((coker_functor_proj (homological_complex V c)).app (arrow.mk i))
                                     (coker_functor_degreewise_SES i) ℓ m hm,
    have LES2 := six_term_exact_seq j ((coker_functor_proj (homological_complex V c)).app (arrow.mk j))
                                      (coker_functor_degreewise_SES j) ℓ m hm,
    refine abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso sq1 sq2 sq3 sq4 _ _ _ _ _ _,
    { exact (exact_iff_exact_seq _ _).mpr (LES1.extract 0 2) },
    { exact (exact_iff_exact_seq _ _).mpr (LES1.extract 1 2) },
    { exact (exact_iff_exact_seq _ _).mpr (LES1.extract 2 2) },
    { exact (exact_iff_exact_seq _ _).mpr (LES2.extract 0 2) },
    { exact (exact_iff_exact_seq _ _).mpr (LES2.extract 1 2) },
    { exact (exact_iff_exact_seq _ _).mpr (LES2.extract 2 2) } }
end

lemma homological_complex.is_iso_of_degreewise_is_iso [has_zero_morphisms V]
  {ι : Type*} {c : complex_shape ι} 
  {C D : homological_complex V c} (f : C ⟶ D) (h : ∀ i, category_theory.is_iso (f.f i))
  : category_theory.is_iso f :=
begin
  convert is_iso.of_iso (hom.iso_of_components (λ i, as_iso (f.f i)) _),
  swap, { intros, rw [as_iso_hom, as_iso_hom], exact f.comm i j },
  symmetry, ext : 2, exact hom.iso_of_components_hom_f _ _ _,
end

end general_abelian_category

section chain_complex

universes u u' v v'

parameters {C : Type u} {V : Type v} [category.{u'} C] [category.{v'} V]
parameters [preadditive V] [has_equalizers V] [has_images V] [has_image_maps V] [has_cokernels V]

def chain_complex.mk_natural_chain_homotopy
  {F G : C ⥤ chain_complex V ℕ}
  {α β : F ⟶ G}
  (s : Π n, (F ⋙ homological_complex.eval V _ n) ⟶ (G ⋙ homological_complex.eval V _ (n + 1)))
  (H0 : ∀ X, (nat_trans.app α X).f 0 = ((s 0).app X ≫ (G.obj X).d 1 0) + (nat_trans.app β X).f 0)
  (H : ∀ n X, (nat_trans.app α X).f (n + 1)
            = ((F.obj X).d (n + 1) n ≫ (s n).app X)
            + ((s (n + 1)).app X ≫ (G.obj X).d (n + 2) (n + 1))
            + (nat_trans.app β X).f (n + 1))
  : natural_chain_homotopy α β := {
    to_chain_htpy := λ X, { hom := λ j i, if h : j + 1 = i 
                                          then eq.rec ((s j).app X) h
                                          else 0,
                            zero' := λ j i h, dite_eq_right_iff.mpr (λ h', absurd h' h),
                            comm := by { intro n,
                                         cases n,
                                         { simp, exact H0 X },
                                         { simp, exact H n X } } },
    naturality := λ X Y f i j h, by { dsimp at h, subst h, simp, exact (s j).naturality' f } 
  }

def chain_complex.mk_natural_chain_homotopy_rec 
  {F G : C ⥤ chain_complex V ℕ}
  {α β : F ⟶ G}
  (init : (F ⋙ homological_complex.eval V _ 0) ⟶ (G ⋙ homological_complex.eval V _ 1))
  (Hinit : ∀ X, (α.app X).f 0 = (nat_trans.app init X ≫ (G.obj X).d 1 0) + (β.app X).f 0)
  (step : Π (n : ℕ) (s : (F ⋙ homological_complex.eval V _ n)
                       ⟶ (G ⋙ homological_complex.eval V _ (n + 1))),
            (∀ X, ((α.app X).f (n + 1)) ≫ (G.obj X).d (n + 1) n
                = (((F.obj X).d (n + 1) n ≫ nat_trans.app s X) + (β.app X).f (n + 1))
                  ≫ (G.obj X).d (n + 1) n)
            → ((F ⋙ homological_complex.eval V _ (n + 1))
              ⟶ (G ⋙ homological_complex.eval V _ (n + 2))))
  (Hstep : ∀ (n : ℕ) (s : (F ⋙ homological_complex.eval V _ n)
                       ⟶ (G ⋙ homological_complex.eval V _ (n + 1)))
             (h : (∀ X, ((α.app X).f (n + 1)) ≫ (G.obj X).d (n + 1) n
                = (((F.obj X).d (n + 1) n ≫ nat_trans.app s X) + (β.app X).f (n + 1))
                  ≫ (G.obj X).d (n + 1) n)),
             ∀ X, (nat_trans.app α X).f (n + 1)
                = ((F.obj X).d (n + 1) n ≫ s.app X)
                + ((step n s h).app X ≫ (G.obj X).d (n + 2) (n + 1))
                + (nat_trans.app β X).f (n + 1))
  : natural_chain_homotopy α β :=
  chain_complex.mk_natural_chain_homotopy
    (λ k,
      (@nat.rec (λ n, Σ' (s : (F ⋙ homological_complex.eval V _ n)
                            ⟶ (G ⋙ homological_complex.eval V _ (n + 1))), 
                        ∀ X, ((α.app X).f (n + 1)) ≫ (G.obj X).d (n + 1) n
                           = (((F.obj X).d (n + 1) n ≫ nat_trans.app s X) + (β.app X).f (n + 1))
                              ≫ (G.obj X).d (n + 1) n)
                ⟨init, by { intro X,
                            rw (α.app X).comm',
                            rw Hinit,
                            simp,
                            apply complex_shape.down_mk, refl }⟩
                (λ n p, ⟨step n p.1 p.2, 
                        by { intro X,
                             rw (α.app X).comm',
                             rw Hstep n p.1 p.2,
                             simp,
                             apply complex_shape.down_mk, refl }⟩)
                k).fst)
    Hinit
    (by { intros n X, simp, apply Hstep })

-- I don't know the rules on when instances should be global
instance [has_zero_object V] (C : chain_complex V ℕ)
  : is_iso (kernel_subobject (C.d_from 0)).arrow :=
  by { rw C.d_from_eq_zero chain_complex.next_nat_zero,
       exact limits.is_iso_kernel_subobject_zero_arrow }

end chain_complex

section Modules

universes u u' v v'

parameters {C : Type u} {R : Type v} [category.{u'} C] [comm_ring R]
parameters {ι : Type} {c : complex_shape ι}

lemma all_eq_zero_of_iso_zero {M : Module.{v'} R} (H : is_isomorphic M 0) (x : M) : x = 0 :=
  congr_fun (congr_arg coe_fn (id_eq_zero_of_iso_zero M H)) x

lemma iso_zero_of_id_eq_zero (M : Module.{v'} R) (h : 𝟙 M = 0) : is_isomorphic M 0 :=
    ⟨is_zero.iso_zero (@Module.is_zero_of_subsingleton _ _ M
                         ⟨λ x y, calc x = (𝟙 M : M ⟶ M) x : rfl
                                    ... = (0 : M ⟶ M) x   : congr_fun (congr_arg _ h) x
                                    ... = (0 : M ⟶ M) y   : rfl
                                    ... = (𝟙 M : M ⟶ M) y : (congr_fun (congr_arg _ h) y).symm⟩)⟩

lemma Module.to_homology.homomorphism (C : homological_complex (Module.{v'} R) c) (i : ι)
  : @is_linear_map R (linear_map.ker (C.d_from i)) (C.homology i) _ _ _ _ _
      (@Module.to_homology R _ ι c C i) := by {
    delta Module.to_homology, delta Module.to_cycles,
    delta homology.π, delta Module.to_kernel_subobject,
    constructor; intros; simp
  }

lemma Module.to_cycles.homomorphism (C : homological_complex (Module.{v'} R) c) (i : ι)
  : is_linear_map R (@Module.to_cycles R _ ι c C i) := by {
    delta Module.to_cycles, delta Module.to_kernel_subobject,
    constructor; intros; simp
  }

lemma Module.to_homology_def 
  (C : homological_complex (Module.{v'} R) c) {i : ι}
  : is_linear_map.mk' _ (Module.to_homology.homomorphism C i)
  = Module.as_hom_right (is_linear_map.mk' _ (Module.to_cycles.homomorphism C i))
  ≫ homology.π (C.d_to i) (C.d_from i) _ := by { ext : 1, refl }

lemma Module.to_cycles_def
  (C : homological_complex (Module.{v'} R) c) {i : ι}
  : Module.as_hom_right (is_linear_map.mk' _ (Module.to_cycles.homomorphism C i))
  = (category_theory.limits.kernel_subobject_iso (C.d_from i)
    ≪≫ Module.kernel_iso_ker (C.d_from i)).inv := by { ext : 1, refl }

lemma Module.to_cycles_is_iso (C : homological_complex (Module.{v'} R) c) (i : ι)
  : is_iso (Module.as_hom_right (is_linear_map.mk' _ (Module.to_cycles.homomorphism C i))) :=
  by { rw Module.to_cycles_def, apply is_iso.of_iso_inv }

lemma Module.to_homology_comp_homology_functor_map
  {X Y : homological_complex (Module.{v'} R) c} (f : X ⟶ Y) (i : ι)
  : Module.as_hom_right (@is_linear_map.mk' R (linear_map.ker (X.d_from i)) (X.homology i)
                                            _ _ _ _ _ 
                                            Module.to_homology
                                            (Module.to_homology.homomorphism X i))
  ≫ (homology_functor (Module R) c i).map f
  = Module.of_hom 
      (linear_map.cod_restrict (linear_map.ker (Y.d_from i)) 
        (linear_map.dom_restrict (f.f i) (linear_map.ker (X.d_from i)))
        (by intros; simp))
  ≫ Module.as_hom_right (is_linear_map.mk' Module.to_homology
                                           (Module.to_homology.homomorphism Y i)) :=
begin 
  apply linear_map.ext, intros x, cases x, simp [Module.as_hom_right], delta Module.to_homology,
  congr, transitivity, apply Module.cycles_map_to_cycles, refl
end

-- The version in mathlib fixed v' to be v for some reason
lemma Module.cokernel_π_ext'
  {M N : Module.{v'} R} (f : M ⟶ N) {x y : N} (m : M) (w : x = y + f m)
  : cokernel.π f x = cokernel.π f y := by { subst w, simp }

def Module.range_to_ker {A B C : Module.{v'} R} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  : Module.of R (linear_map.range f) ⟶ Module.of R (linear_map.ker g) := {
    to_fun := λ x, ⟨x.val, by { obtain ⟨x, y, h⟩ := x, subst h, simp, rw [← comp_apply, w], refl }⟩,
    map_add' := by { rintros ⟨x, x', hx⟩ ⟨y, y', hy⟩, simp },
    map_smul' := by { rintros r ⟨x, x', hx⟩, apply subtype.eq, simp },
  }

@[simp]
lemma Module.range_to_ker_subtype_ker
  {A B C : Module.{v'} R} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  : Module.range_to_ker f g w ≫ Module.as_hom_right (linear_map.ker g).subtype
  = Module.as_hom_right (linear_map.range f).subtype := by { ext, refl }

lemma Module.image_to_kernel'_kernel_iso_ker
  {A B C : Module.{v'} R} (f : A ⟶ B) (g : B ⟶ C) (w : f ≫ g = 0)
  : (Module.image_iso_range f).inv ≫ image_to_kernel' f g w
  =  Module.range_to_ker f g w ≫ (Module.kernel_iso_ker g).inv :=
begin
  rw [iso.inv_comp_eq, ← category.assoc, iso.eq_comp_inv],
  apply (@cancel_mono _ _ _ _ _ _ (Module.mono_as_hom'_subtype (linear_map.ker g)) _ _).mp,
  rw [category.assoc, category.assoc, Module.range_to_ker_subtype_ker],
  simp [Module.as_hom_right, image_to_kernel'], 
  symmetry, apply Module.image_iso_range_hom_subtype
end

-- Possible this proof could be prettified/sped up
lemma Module.to_homology_ext
  {X : homological_complex (Module.{v'} R) c}
  {i j : ι}
  {x y : linear_map.ker (X.d_from j)}
  (m : X.X i) (hm : x.val = y.val + X.d i j m) 
  : Module.to_homology x = Module.to_homology y :=
  Module.cokernel_π_ext'
    (image_to_kernel (X.d_to j) (X.d_from j) (X.d_to_comp_d_from j))
    ((image_subobject_iso (X.d_to j)).inv
      ((Module.image_iso_range (X.d_to j)).inv
        ⟨X.d i j m, 
          by { by_cases c.rel i j,
               { rw X.d_to_eq h,
                 existsi (X.X_prev_iso h).inv m,
                 simp },
               { rw X.shape' i j h, apply submodule.zero_mem } }⟩))
    (by { by_cases c.rel i j,
          { have h1 : X.d i j m ∈ linear_map.ker (X.d_from j),
            { rw [linear_map.mem_ker, ← X.X_prev_iso_comp_d_to h,
                  comp_apply, ← comp_apply, d_to_comp_d_from],
              refl },
            transitivity Module.to_cycles y + Module.to_cycles ⟨X.d i j m, h1⟩,
            { rw ← is_linear_map.map_add (Module.to_cycles.homomorphism X j),
              congr, apply subtype.eq, exact hm },
            congr,
            rw [← comp_apply (iso.inv _), ← image_to_kernel'_kernel_subobject_iso,
                comp_apply, ← comp_apply (iso.inv _), Module.image_to_kernel'_kernel_iso_ker],
            apply (kernel_subobject_iso (X.d_from j)).eq_app_inv_of_app_hom_eq,
            apply iso.eq_app_inv_of_app_hom_eq,
            apply subtype.eq, 
            delta Module.to_cycles,
            simp [Module.range_to_ker, Module.to_kernel_subobject, Module.kernel_iso_ker] },
          { rw X.shape' i j h at hm, 
            rw subtype.eq (eq.trans hm (add_zero _)),
            symmetry, refine eq.trans _ (add_zero _),
            have : ∀ h' : X.d i j m ∈ linear_map.range (X.d_to j), 
                    (⟨X.d i j m, h'⟩ : {t // t ∈ linear_map.range (X.d_to j)}) = 0,
            { intro, simp, rw X.shape' i j h, refl },
            rw this,
            simp } })

lemma Module.homology_ext''
  (C D : homological_complex (Module.{v'} R) c)
  {h k : C ⟶ D} (i : ι)
  (w : ∀ (x : C.X i), C.d_from i x = 0 →
       ∃ (j : ι) (y : D.X j), h.f i x = k.f i x + D.d j i y)
  : (homology_functor (Module.{v'} R) c i).map h = (homology_functor (Module.{v'} R) c i).map k :=
begin
  apply Module.homology_ext', intro x, cases x with x hx,
  rw [homology_functor_map, homology_functor_map, homology.π_map_apply, homology.π_map_apply],
  delta kernel_subobject_map, dsimp [hom.sq_from],
  rw [Module.cycles_map_to_cycles, Module.cycles_map_to_cycles],
  obtain ⟨j, y, hy⟩ := w x hx,
  exact Module.to_homology_ext y hy
end

lemma homological_complex.range_d_eq
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  : linear_map.range (C.d i j)
  = linear_map.range (C.boundaries_to_cycles j ≫ (C.cycles j).arrow) :=
begin
  delta boundaries_to_cycles,
  rw image_to_kernel_arrow,
  symmetry, apply ((Module.subobject_Module _).apply_eq_iff_eq_symm_apply _ _).mpr,
  dsimp [Module.subobject_Module, order_iso.symm, rel_iso.symm],
  refine eq.trans _
          (eq.trans (image_subobject_iso_comp (C.X_prev_iso hij).hom (C.d i j))
                    _),
  { congr, apply homological_complex.d_to_eq },
  { refine eq.trans (image_subobject_mono _).symm (eq.trans _ (image_subobject_mono _)),
    refine eq.trans _ (image_subobject_iso_comp (Module.image_iso_range (C.d i j)).hom _),
    congr, symmetry, apply Module.image_iso_range_hom_subtype }
end

def homological_complex.exists_preim_cycle_of_to_homology_zero
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  (x : C.X j) (is_cycle : C.d_from j x = 0) (H : Module.to_homology ⟨x, is_cycle⟩ = 0)
  : ∃ t : C.X i, (C.d i j) t = x :=
begin
  apply linear_map.mem_range.mp,
  rw C.range_d_eq hij,
  change (x ∈ linear_map.range ((C.cycles j).arrow.comp (C.boundaries_to_cycles j))),
  rw linear_map.range_comp (C.boundaries_to_cycles j) (C.cycles j).arrow,
  rw submodule.mem_map,
  refine ⟨Module.to_cycles ⟨x, is_cycle⟩, _, Module.to_kernel_subobject_arrow _⟩,
  apply (submodule.quotient.mk_eq_zero _).mp,
  have : function.injective (Module.cokernel_iso_range_quotient (C.boundaries_to_cycles j)).inv,
  { apply function.left_inverse.injective, intro, apply iso.inv_hom_id_apply },
  refine this (eq.trans (eq.trans _ H) (map_zero _).symm),
  delta Module.to_homology, delta homology.π,
  rw ← Module.range_mkq_cokernel_iso_range_quotient_inv, refl
end

noncomputable
def homological_complex.preim_cycle_of_to_homology_zero
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  (x : C.X j) (is_cycle : C.d_from j x = 0) (H : Module.to_homology ⟨x, is_cycle⟩ = 0)
  : C.X i :=
@classical.some (C.X i) (λ y, C.d i j y = x)
                (homological_complex.exists_preim_cycle_of_to_homology_zero C hij x is_cycle H)

lemma homological_complex.preim_cycle_of_to_homology_zero_spec
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  (x : C.X j) (is_cycle : C.d_from j x = 0) (H : Module.to_homology ⟨x, is_cycle⟩ = 0)
  : (C.d i j) (homological_complex.preim_cycle_of_to_homology_zero C hij x is_cycle H) = x :=
@classical.some_spec (C.X i) (λ y, C.d i j y = x)
                     (homological_complex.exists_preim_cycle_of_to_homology_zero C hij x is_cycle H)

noncomputable
def homological_complex.preim_cycle_of_homology_zero
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  (x : C.X j) (is_cycle : C.d_from j x = 0) (H : is_isomorphic (C.homology j) 0) 
  : C.X i :=
homological_complex.preim_cycle_of_to_homology_zero C hij x is_cycle (all_eq_zero_of_iso_zero H _)

lemma homological_complex.preim_cycle_of_homology_zero_spec
  (C : homological_complex (Module.{v'} R) c) {i j : ι} (hij : c.rel i j)
  (x : C.X j) (is_cycle : C.d_from j x = 0) (H : is_isomorphic (C.homology j) 0)
  : C.d i j (homological_complex.preim_cycle_of_homology_zero C hij x is_cycle H) = x :=
homological_complex.preim_cycle_of_to_homology_zero_spec C hij x is_cycle
                                                         (all_eq_zero_of_iso_zero H _)

lemma homological_complex.exists_preim_homology_class
  (C : homological_complex (Module.{v'} R) c) {i : ι} (y : C.homology i)
  : ∃ (x : C.X i) (h : C.d_from i x = 0), Module.to_homology ⟨x, h⟩ = y :=
begin
  suffices : y ∈ linear_map.range (is_linear_map.mk' _ (Module.to_homology.homomorphism C i)),
  { obtain ⟨⟨y, h⟩, h'⟩ := linear_map.mem_range.mp this, existsi y, existsi h, exact h' },
  rw [Module.to_homology_def, Module.comp_def],
  rw linear_map.range_comp,
  rw linear_map.range_eq_top.mpr,
  { rw submodule.map_top, revert y, apply submodule.eq_top_iff'.mp,
    rw linear_map.range_eq_top.mpr,
    delta homology.π,
    rw ← Module.range_mkq_cokernel_iso_range_quotient_inv,
    rw coe_comp, apply function.surjective.comp,
    refine function.left_inverse.surjective (iso.hom_inv_id_apply _),
    apply submodule.mkq_surjective },
  { exact function.right_inverse.surjective
            (@is_iso.inv_hom_id_apply _ _ _ _ _ (Module.to_cycles_is_iso C i) _) }
end

noncomputable
def homological_complex.preim_of_homology_class
  (C : homological_complex (Module.{v'} R) c) {i : ι} (y : C.homology i) 
  : C.X i :=
  classical.some (homological_complex.exists_preim_homology_class C y)

def homological_complex.preim_of_homology_class_spec
  (C : homological_complex (Module.{v'} R) c) {i : ι} (y : C.homology i)
  : ∃ (h : C.d_from i (homological_complex.preim_of_homology_class C y) = 0),
      Module.to_homology ⟨homological_complex.preim_of_homology_class C y, h⟩ = y :=
  classical.some_spec (homological_complex.exists_preim_homology_class C y)

lemma Module.to_homology_eq_zero
  {X : homological_complex (Module.{v'} R) c}
  {i j : ι} (hij : c.rel i j)
  {x : linear_map.ker (X.d_from j)}
  : x.val ∈ linear_map.range (X.d i j) ↔ Module.to_homology x = 0 :=
begin
  split,
  { rintro ⟨w, h⟩,
    transitivity Module.to_homology (0 : linear_map.ker (X.d_from j)),
    apply Module.to_homology_ext w, symmetry, simp, exact h,
    apply (Module.to_homology.homomorphism _ _).map_zero },
  { intro h, cases x with x hx,
    obtain ⟨y, hy⟩ := homological_complex.exists_preim_cycle_of_to_homology_zero X hij x hx h,
    exact ⟨y, hy⟩ }
end

lemma Module.to_homology_eq_zero'
  {X : homological_complex (Module.{v'} R) c}
  {i : ι} (hi : c.prev i = none)
  {x : linear_map.ker (X.d_from i)}
  : x = 0 ↔ Module.to_homology x = 0 :=
begin
  split,
  { intro h, subst h, exact is_linear_map.map_zero (Module.to_homology.homomorphism X i) },
  { intro h, delta Module.to_homology at h,
    suffices : Module.to_cycles x = 0,
    { delta Module.to_cycles Module.to_kernel_subobject at this,
      convert congr_arg (kernel_subobject_iso (X.d_from i) ≪≫ Module.kernel_iso_ker (X.d_from i)).hom this;
      simp },
    { generalize_hyp : Module.to_cycles x = y at ⊢ h,
      delta homology.π at h,
      suffices : is_iso (cokernel.π (image_to_kernel (X.d_to i) (X.d_from i) (X.d_to_comp_d_from i))),
      { refine eq.trans _ (eq.trans (congr_arg (@inv _ _ _ _ _ this) h) (map_zero _)), simp },
      convert cokernel.π_zero_is_iso,
      all_goals
      { apply zero_of_source_iso_zero,
        refine (image_subobject_iso _).trans _,
        apply category_theory.limits.image_zero',
        delta homological_complex.d_to, rw hi } } }
end

end Modules

section retract

universes v v'
parameters {R : Type v} [comm_ring R]
parameters {ι : Type} {c : complex_shape ι}


/-
We should be able to prove that iterating barycentric subdivision enough times,
depending on the input simplex, gives a chain map C_*(X) -> C_*(X) which is a retraction onto
the subcomplex of chains bounded by an open cover 𝒰, as in Hatcher. But this subtly requires that
if τ is a face of σ and B^k(σ) ∈ C_n^𝒰(X) then B^k(τ) ∈ C_n^𝒰(X).
This follows from the fact that B is secretly a morphism of simplicial abelian groups
Sing_•(X) → Sing_•(X), and so commutes with face maps. But in a general chain complex we don't
have access to the face maps (Dold Kan is *not* about the Moore complex, but the normalized Moore complex)
and so it's awkward to state the lemma. Also proving this would be a lot of work
-/

-- local attribute [instance] classical.prop_decidable 

def homotopy.iterate {V : Type v} [category.{v'} V] [preadditive V] 
  {C : homological_complex V c} {f : C ⟶ C}
  (s : homotopy (𝟙 C) f)
  : Π (k : ℕ), homotopy (𝟙 C) (f ^ k : End C)
| 0       := homotopy.refl (𝟙 C)
| (k + 1) := (homotopy.iterate k).trans (s.symm.comp_left_id (f ^ k : End C)).symm

lemma chain_map_iterate {V : Type v} [category.{v'} V] [has_zero_morphisms V]
  {C : homological_complex V c} (f : C ⟶ C)
  (k : ℕ) (i : ι) : (f ^ k : End C).f i = (f.f i ^ k : End (C.X i)) :=
begin
  induction k with k ih,
  { refl },
  { rw [← npow_eq_pow, ← npow_eq_pow, monoid.npow_succ', monoid.npow_succ'],
    exact congr_arg2 category_struct.comp ih rfl }
end

-- lemma homotopy.iterate_as_sum {V : Type v} [category.{v'} V] [preadditive V]
--   {C : homological_complex V c} {f : C ⟶ C}
--   (s : homotopy (𝟙 C) f) (k : ℕ) (i j : ι)
--   : (s.iterate k).hom i j = finset.univ.sum (λ p : fin k, (f^(p : ℕ) : End C).f i ≫ s.hom i j) :=
-- begin
--   by_cases c.rel j i,
--   { induction k with k ih,
--     { refl },
--     { simp [homotopy.iterate],
--       rw fin.sum_univ_cast_succ,
--       simp,
--       rw ih,
--       congr,
--       simp [homotopy.symm, homotopy.comp_left_id] } },
--   { rw (s.iterate k).zero i j h, simp_rw s.zero i j h, simp }
-- end

-- noncomputable
-- def homotopy.iter_until_in_subcomplex
--   {ι' : ι → Type}
--   {C : homological_complex (Module.{v'} R) c}
--   (b : Π (i : ι), basis (ι' i) R (C.X i))
--   (M : Π (i : ι), submodule R (C.X i))
--   (f : C ⟶ C)
--   (H : ∀ i x, ∃ k, (f.f i)^[k] x ∈ M i)
--   (s : homotopy (𝟙 C) f) (i j : ι) : C.X i ⟶ C.X j :=
--   (b i).constr R (λ ℓ, (s.iterate (nat.find (H i (b i ℓ)))).hom i j (b i ℓ))

-- lemma d_next_of_iter_until_in_subcomplex_on_basis 
--   {ι' : ι → Type}
--   {C : homological_complex (Module.{v'} R) c}
--   (b : Π (i : ι), basis (ι' i) R (C.X i))
--   (M : Π (i : ι), submodule R (C.X i))
--   (f : C ⟶ C)
--   (H : ∀ i x, ∃ k, (f.f i)^[k] x ∈ M i)
--   (s : homotopy (𝟙 C) f) (i : ι) (ℓ : ι' i)
--   : prev_d i (homotopy.iter_until_in_subcomplex b M f H s) (b i ℓ)
--   = prev_d i (s.iterate (nat.find (H i (b i ℓ)))).hom (b i ℓ) :=
-- begin
-- destruct c.prev i,
-- { intro h, delta prev_d, simp, rw h },
-- { rintros ⟨j, hij⟩ h, delta prev_d, simp, rw h, simp,
--   refine congr_arg _ _,
--   exact basis.constr_basis _ _ _ _ }
-- end

-- noncomputable
-- def retract_free_of_eventually_in_submodule
--   {ι' : ι → Type}
--   (C : homological_complex (Module.{v'} R) c)
--   (b : Π (i : ι), basis (ι' i) R (C.X i))
--   (M : Π (i : ι), submodule R (C.X i))
--   (f : C ⟶ C)
--   (H : ∀ i x, ∃ k, (f.f i)^[k] x ∈ (M i))
--   (s : homotopy (𝟙 C) f)
--   : C ⟶ C := {
--     f := λ i, (𝟙 (C.X i)) - (d_next i) (homotopy.iter_until_in_subcomplex b M f H s)
--                           - (prev_d i) (homotopy.iter_until_in_subcomplex b M f H s),
--     comm' := by {
--       intros i j hij,
--       apply (b i).ext, intro ℓ,
--       simp, rw sub_right_comm,
--       congr, 
--       { repeat { rw ← comp_apply },
--         refine congr_fun (congr_arg coe_fn _) _,
--         transitivity (0 : C.X i ⟶ C.X j),
--         { rw ← d_from_comp_X_next_iso _ hij,
--           swap, apply_instance, 
--           rw ← category.assoc (C.d_to i), simp },
--         { rw ← X_prev_iso_comp_d_to _ hij,
--           rw [category.assoc, ← category.assoc (C.d_to j)], simp } },
--       { repeat { rw ← comp_apply },
--         refine congr_fun (congr_arg coe_fn _) _,
--         rw [← category.assoc, ← d_next_eq_d_from_from_next, d_next_eq _ hij],
--         rw category.assoc, refine congr_arg _ _,
--         rw ← prev_d_eq _ hij, simp } } }

-- def retract_free_of_eventually_in_submodule_eventually_in
--   {ι' : ι → Type}
--   (C : homological_complex (Module.{v'} R) c)
--   (b : Π (i : ι), basis (ι' i) R (C.X i))
--   (M : Π (i : ι), submodule R (C.X i))
--   (f : C ⟶ C)
--   (H : ∀ i x, ∃ k, (f.f i)^[k] x ∈ M i)
--   (s : homotopy (𝟙 C) f)
--   (hb : ∀ i j, submodule.map (C.d i j) (M i) ≤ M j)
--   (hs : ∀ i j, submodule.map (s.hom i j) (M i) ≤ M j)
--   (hf : ∀ i, submodule.map (f.f i) (M i) ≤ M i)
--   (hboundary_in_M_only_if : ∀ i ℓ, b i ℓ ∈ M i
--                           → ∀ j m, (b j).repr (C.d i j (b i ℓ)) m ≠ 0 → b j m ∈ M j)
--   : ∀ i, linear_map.range ((retract_free_of_eventually_in_submodule C b M f H s).f i)
--        ≤ M i :=
-- begin
--   have : ∀ i ℓ j m, (b j).repr (C.d i j (b i ℓ)) m ≠ 0
--                   → nat.find (H j (b j m)) ≤ nat.find (H i (b i ℓ)),
--   { intros i ℓ j m h,
--     apply nat.find_le,
--     have := nat.find_spec (H i (b i ℓ)), revert this,
--     generalize : nat.find (H i (b i ℓ)) = k, intro h,
--      },
--   intro i,
--   rw linear_map.range_eq_map,
--   rw ← (b i).span_eq,
--   rw submodule.map_span_le,
--   rintros x ⟨ℓ, h⟩, subst h,
--   dsimp [retract_free_of_eventually_in_submodule],
--   rw d_next_of_iter_until_in_subcomplex_on_basis,
--   have := (s.iterate (nat.find (H i (b i ℓ)))).comm i,
--   rw ← sub_eq_iff_eq_add at this,
--   symmetry' at this, rw add_comm at this, symmetry' at this, rw ← sub_eq_iff_eq_add at this,
--   rw ← this,
--   simp,
--   rw [sub_right_comm, sub_sub _ _ ((from_next i (s.iterate _).hom _)), ← sub_add],
--   simp, rw add_sub_assoc,
--   apply submodule.add_mem,
--   { convert nat.find_spec (H i (b i ℓ)),
--     generalize : nat.find (H i (b i ℓ)) = k,
--     induction k with k ih,
--     { refl },
--     { rw nat.iterate_succ,
--       rw ← npow_eq_pow,
--       rw monoid.npow_succ',
--       rw ← ih,
--       refl } },
--   {  }
--   -- refine eq.trans (congr_arg2 _ _ _) (add_zero _),
--   -- { transitivity (f ^ 0 : End C).f i (b i ℓ),
--   --   { congr, simp,
--   --     exact submodule.subset_span ⟨ℓ, hℓ, rfl⟩ },
--   --   { refl } },
-- end

-- def retract_free_of_eventually_in_submodule_homotopic
--   {ι' : ι → Type}
--   (C : homological_complex (Module.{v'} R) c)
--   (b : Π (i : ι), basis (ι' i) R (C.X i))
--   (b' : Π (i : ι), ι' i → Prop)
--   (f : C ⟶ C)
--   (H : ∀ i x, ∃ k, (f.f i)^[k] x ∈ submodule.span R (b i '' { ℓ | b' i ℓ }))
--   (s : homotopy (𝟙 C) f)
--   (hf : ∀ (i : ι) (ℓ : ι' i), f.f i (b i ℓ) ∈ submodule.span R (b i '' { m | b' i m }))
--   (hb' : ∀ (i j : ι) (ℓ : ι' i), C.d i j (b i ℓ) ∈ submodule.span R (b j '' { m | b' j m }))
--   : homotopy (𝟙 C) (retract_free_of_eventual_retract_on_basis C b (λ j, submodule.span R (b j '' { ℓ | b' j ℓ })) f H s) :=
-- begin
--   admit
-- end

end retract

section Modules

universes u u' v v'

parameters {C : Type u} {R : Type v} [category.{u'} C] [comm_ring R]
parameters {ι : Type} {c : complex_shape ι}

def Module.subcomplex_of_compatible_submodules
  (C : homological_complex (Module.{v'} R) c)
  (M : Π (i : ι), submodule R (C.X i))
  (hcompat : ∀ i j, submodule.map (C.d i j) (M i) ≤ M j)
  : homological_complex (Module.{v'} R) c := {
    X := λ i, Module.of R (M i),
    d := λ i j, linear_map.cod_restrict (M j) 
                                        (linear_map.dom_restrict (C.d i j) (M i))
                                        (λ x, hcompat i j (submodule.mem_map_of_mem x.property)),
    d_comp_d' := by { intros i j k hij hjk, ext, cases x with x hx, 
                      simp, rw ← comp_apply, rw C.d_comp_d, refl },
    shape' := by { intros i j hij, ext, cases x with x hx, simp, rw C.shape' i j hij, refl } }

def Module.subcomplex_of_compatible_submodules_inclusion
  (C : homological_complex (Module.{v'} R) c)
  (M : Π (i : ι), submodule R (C.X i))
  (hcompat : ∀ i j, submodule.map (C.d i j) (M i) ≤ M j)
  : Module.subcomplex_of_compatible_submodules C M hcompat ⟶ C := {
    f := λ i, (M i).subtype
  }

lemma quasi_iso_of_lift_boundaries_and_cycles
  {C D : homological_complex (Module.{v'} R) c} (f : C ⟶ D)
  (h1 : ∀ i j x y, C.d_from j y = 0 → D.d i j x = f.f j y → ∃ z, C.d i j z = y)
  (h2 : ∀ j x, D.d_from j x = 0 → ∃ i y z, C.d_from j y = 0 ∧ f.f j y = x + D.d i j z)
  : quasi_iso f :=
begin
  constructor,
  intro i,
  suffices : function.bijective ((homology_functor (Module R) c i).map f),
  { let f' := linear_equiv.of_bijective _ this.left this.right,
    constructor,
    refine exists.intro f'.symm _,
    split; apply Module.homology_ext'; intro, { apply f'.left_inv }, { apply f'.right_inv } },
  split,
  { rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
    intros x hx,
    obtain ⟨h, h'⟩ := C.preim_of_homology_class_spec x,
    generalize_hyp : C.preim_of_homology_class x = x' at h h', subst h',
    have := congr_arg linear_map.to_fun (@Module.to_homology_comp_homology_functor_map R _ ι c C D f i),
    replace this := congr_fun this (⟨x', h⟩ : linear_map.ker (C.d_from i)),
    replace this := eq.trans this.symm hx,
    simp [Module.as_hom_right] at this,
    destruct (c.prev i),
    { intro h', rw ← Module.to_homology_eq_zero' h' at this ⊢,
      obtain ⟨z, hz⟩ := h1 i i 0 x' h (eq.trans (map_zero _) (subtype.ext_iff_val.mp this.symm)),
      have : ¬ c.rel i i, { intro hi', rw c.prev_eq_some hi' at h', injection h' },
      rw C.shape i i this at hz, symmetry, exact subtype.eq hz },
    { rintro ⟨j, hij⟩ _,
      rw ← Module.to_homology_eq_zero hij,
      rw ← Module.to_homology_eq_zero hij at this,
      simp at this, obtain ⟨y, hy⟩ := this,
      exact h1 j i y x' h hy } },
  { intro x,
    obtain ⟨h, h'⟩ := D.preim_of_homology_class_spec x,
    generalize_hyp : D.preim_of_homology_class x = x' at h h', subst h',
    obtain ⟨j, y, z, hy, hz⟩ := h2 i x' h,
    existsi Module.to_homology ⟨y, hy⟩,
    have := congr_arg linear_map.to_fun (@Module.to_homology_comp_homology_functor_map R _ ι c C D f i),
    replace this := congr_fun this (⟨y, hy⟩ : linear_map.ker (C.d_from i)),
    refine eq.trans this _,
    exact Module.to_homology_ext z hz }
end

lemma subcomplex_inclusion_quasi_iso_of_pseudo_projection
  {C : homological_complex (Module.{v'} R) c}
  (M : Π (i : ι), submodule R (C.X i))
  (hcompat : ∀ i j, submodule.map (C.d i j) (M i) ≤ M j)
  (p : C ⟶ C) (s : homotopy (𝟙 C) p)
  (hp_eventual : ∀ i x, ∃ k, (p.f i)^[k] x ∈ M i)
  (hp : ∀ i, submodule.map (p.f i) (M i) ≤ M i)
  (hs : ∀ i j, submodule.map (s.hom i j) (M i) ≤ M j)
  : quasi_iso (Module.subcomplex_of_compatible_submodules_inclusion C M hcompat) :=
begin
  have hp_iter : ∀ i k {x}, x ∈ M i → ((p.f i)^[k] x) ∈ M i, 
  { intros i k x hx, induction k with k ih,
    { exact hx },
    { rw nat.iterate_succ,
      refine hp i _,
      existsi ((p.f i)^[k] x), exact ⟨ih, rfl⟩ } },
  have hs_iter : ∀ i j k, submodule.map ((s.iterate k).hom i j) (M i) ≤ M j,
  { intros i j k, specialize hs i j,
    rw submodule.map_le_iff_le_comap at ⊢ hs,
    intros x hx, simp,
    induction k with k ih,
    { exact zero_mem _, },
    { simp [homotopy.iterate],
      apply submodule.add_mem,
      { exact ih },
      { refine hs _, rw chain_map_iterate p k,
        rw concrete_category.pow_eq_iter, 
        exact hp_iter i k hx } } },
  apply quasi_iso_of_lift_boundaries_and_cycles, 
  { intros i j x y hy hx,
    obtain ⟨k, hk⟩ := hp_eventual i x,
    refine exists.intro (⟨(s.iterate k).hom j i y.val, _⟩ + ⟨(p.f i)^[k] x, hk⟩) _,
    { refine hs_iter j i k _, exact submodule.mem_map_of_mem y.property },
    { ext,
      delta Module.subcomplex_of_compatible_submodules,
      delta Module.subcomplex_of_compatible_submodules_inclusion at hx,
      simp at ⊢ hx,
      refine eq.trans _ hx,
      by_cases (c.rel i j),
      { rw ← hx,
        rw ← comp_apply _ ((s.iterate k).hom j i), 
        rw ← d_next_eq _ h,
        dsimp,
        have := (s.iterate k).comm i,
        rw ← sub_eq_iff_eq_add at this,
        rw ← sub_eq_iff_eq_add at this,
        rw ← this,
        simp,
        rw (_ : (C.d i j) (C.d_to i (to_prev i (s.iterate k).hom x)) = 0),
        rw sub_zero,
        rw sub_add,
        convert sub_zero _,
        { rw sub_eq_zero,
          refine congr_arg _ _,
          rw chain_map_iterate,
          rw concrete_category.pow_eq_iter },
        { rw ← homological_complex.d_from_comp_X_next_iso _ h,
          rw ← comp_apply,
          rw ← category.assoc,
          simp, apply_instance } },
      { rw C.shape' i j h, simp } } },
  { intros j x hx,
    obtain ⟨k, hk⟩ := hp_eventual j x,
    have : x - ((p.f j)^[k] x) = prev_d j (s.iterate k).hom x,
    { have := (s.iterate k).comm j,
      rw ← sub_eq_iff_eq_add at this,
      transitivity d_next j (s.iterate k).hom x + prev_d j (s.iterate k).hom x,
      { convert congr_fun (congr_arg coe_fn this) x,
        rw [chain_map_iterate, concrete_category.pow_eq_iter] },
      { symmetry,
        convert add_zero _,
        destruct (c.next j),
        { intro h, delta d_next, rw h, simp },
        { rintros ⟨i, h⟩ _,
          rw d_next_eq _ h,
          dsimp,
          rw ← d_from_comp_X_next_iso _ h,
          dsimp, rw hx, simp } } },
    rw exists_comm, refine ⟨⟨_, hk⟩, _⟩,
    simp_rw [exists_and_distrib_left],
    split, 
    { destruct (c.next j),
      { intro h', delta homological_complex.d_from, rw h', simp },
      { rintros ⟨ℓ, h'⟩ _, rw d_from_eq _ h', simp,
        convert map_zero _,
        dsimp [Module.subcomplex_of_compatible_submodules],
        apply subtype.eq, simp,
        rw [← concrete_category.pow_eq_iter, ← chain_map_iterate],
        rw [← comp_apply, homological_complex.hom.comm, comp_apply],
        rw [← d_from_comp_X_next_iso _ h', comp_apply, hx], simp } },
    destruct (c.prev j),
    { intro h,
      existsi j, refine ⟨0, _⟩,
      simp,
      delta prev_d at this, rw h at this, simp at this,
      rw sub_eq_zero at this, symmetry' at this, exact this },
    { rintros ⟨i, hi⟩ _, existsi i,
      rw prev_d_eq _ hi at this, dsimp at this, rw sub_eq_iff_eq_add at this,
      existsi - (s.iterate k).hom j i x,
      rw [map_neg, ← sub_eq_add_neg, eq_sub_iff_add_eq],
      symmetry, rw add_comm, exact this } }
end

end Modules
