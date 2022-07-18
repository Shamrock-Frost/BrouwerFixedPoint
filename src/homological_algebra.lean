import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy

import for_mathlib.homological_complex_abelian

import .category_theory .linear_algebra

section 

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
  ext, simp,
  suffices : kernel_subobject_map (homological_complex.hom.sq_from f i) = 0,
  { rw this, simp },
  ext, simp,
  rw H, simp
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


protected def parallel_pair_comp_has_colim 
  {V : Type*} [category V] {ι : Type} {c : complex_shape ι}
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
                 simp, } } }

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
  {X Y : homological_complex (Module R) c} (f : X ⟶ Y) (i : ι)
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
  ext, cases x, simp [Module.as_hom_right], delta Module.to_homology, congr,
  transitivity, apply Module.cycles_map_to_cycles, refl
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

lemma Module.to_homology_eq_zero
  {X : homological_complex (Module.{v'} R) c}
  {i j : ι} (hij : c.rel i j)
  {x : linear_map.ker (X.d_from j)}
  : x.val ∈ linear_map.range (X.d i j) → Module.to_homology x = 0 :=
begin
  rintro ⟨w, h⟩,
  transitivity Module.to_homology (0 : linear_map.ker (X.d_from j)),
  apply Module.to_homology_ext w, symmetry, simp, exact h,
  apply (Module.to_homology.homomorphism _ _).map_zero
end

lemma Module.homology_ext''
  (C D : homological_complex (Module.{v'} R) c)
  {h k : C ⟶ D} (i : ι)
  (w : ∀ (x : C.X i), C.d_from i x = 0 →
       ∃ (j : ι) (y : D.X j), h.f i x = k.f i x + D.d j i y)
  : (homology_functor (Module.{v'} R) c i).map h = (homology_functor (Module.{v'} R) c i).map k :=
begin
  ext, cases x with x hx,
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

end Modules

end