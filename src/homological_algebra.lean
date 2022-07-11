import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy

open category_theory category_theory.limits

-- I do not understand universes

local attribute [instance] category_theory.limits.has_zero_object.has_zero

lemma id_eq_zero_of_iso_zero (V : Type*) [category V] [has_zero_object V] [has_zero_morphisms V]
  (X : V) (H : is_isomorphic X 0) : 𝟙 X = 0 :=
begin
  replace H := H, cases H,
  transitivity H.hom ≫ H.inv, simp,
  transitivity H.hom ≫ 0,
  { congr, ext },
  { apply_instance },
  { simp }
end

section

universes u uhom v vhom w

parameters {C : Type u} [category.{uhom} C] {R : Type v} [comm_ring R]

def homological_complex.mk_nat_trans {V : Type v} [category.{vhom} V] [abelian V]
  {ι : Type w} {c : complex_shape ι}
  {F G : C ⥤ homological_complex V c}
  (η : Π (i : ι), (F ⋙ homological_complex.eval V c i)
                ⟶ (G ⋙ homological_complex.eval V c i))
  (η_comm_ds : ∀ (i j : ι), c.rel i j → ∀ X, (η i).app X ≫ (G.obj X).d i j
                                           = (F.obj X).d i j ≫ (η j).app X)
  : F ⟶ G := {
    app := λ X, { f := λ i, (η i).app X,
                  comm' := by exact λ i j h, η_comm_ds i j h X },
    naturality' := λ X Y f, homological_complex.hom.ext _ _ (funext (λ i, (η i).naturality f))
  }

def homological_complex.d_nat_trans {V : Type v} [category.{vhom} V] [abelian V]
  {ι : Type w} {c : complex_shape ι}
  (F : C ⥤ homological_complex V c)
  (i j : ι) : (F ⋙ homological_complex.eval V c i) ⟶ (F ⋙ homological_complex.eval V c j) := {
    app := λ X, (F.obj X).d i j,
    naturality' := by simp
  }

structure natural_chain_homotopy {V : Type v} [category.{vhom} V] [abelian V]
                                 {ι : Type w} {c : complex_shape ι}
                                 {F G : C ⥤ homological_complex V c}
                                 (α β : F ⟶ G)
                                 : Type (max u (max v (vhom + 1)) w)
                                 :=
(to_chain_htpy : ∀ X, homotopy (nat_trans.app α X) (nat_trans.app β X))
(naturality : ∀ X Y (f : X ⟶ Y) i j, c.rel i j → (F.map f).f j ≫ (to_chain_htpy Y).hom j i
                                                = (to_chain_htpy X).hom j i ≫ (G.map f).f i)

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

lemma category_theory.eq_app_inv_of_app_hom_eq [concrete_category C] {X Y : C} (f : X ≅ Y)
  {x : X} {y : Y} (H : f.hom x = y) : x = f.inv y := 
begin
  transitivity f.inv (f.hom x),
  { simp },
  { rw H }
end

lemma Module.to_homology.homomorphism {ι : Type w} {c : complex_shape ι}
                                      (C : homological_complex (Module.{vhom} R) c) (i : ι)
                                      : @is_linear_map R (linear_map.ker (C.d_from i)) 
                                                         (C.homology i)
                                                         _
                                                         _
                                                         _
                                                         _
                                                         _
                                                         (@Module.to_homology R _ ι c C i) := by {
    delta Module.to_homology, delta Module.to_cycles,
    delta homology.π, delta Module.to_kernel_subobject,
    constructor; intros; simp,
  }

lemma all_eq_zero_of_iso_zero {M : Module.{vhom} R} (H : is_isomorphic M 0) (x : M) : x = 0 :=
  congr_fun (congr_arg coe_fn (id_eq_zero_of_iso_zero _ M H)) x

def exists_preim_cycle_of_to_homology_zero {ι : Type w} {c : complex_shape ι}
                                           (C : homological_complex (Module.{vhom} R) c) (i j : ι)
                                           (hij : c.rel i j)
                                           (x : C.X j) (is_cycle : C.d_from j x = 0)
                                           (H : Module.to_homology ⟨x, is_cycle⟩ = 0)
  : ∃ t : C.X i, (C.d i j) t = x :=
begin
  have : ∃ a, (C.boundaries_to_cycles j) a = Module.to_cycles ⟨x, is_cycle⟩,
  { let := (@Module.cokernel_iso_range_quotient R _ _ _ (C.boundaries_to_cycles j)).symm,
    generalize h : Module.to_cycles ⟨x, is_cycle⟩ = c',
    have is_zero : this.inv (this.hom (submodule.quotient.mk c'))
                  = submodule.quotient.mk c',
    { have hom_inv_id := this.hom_inv_id',
      dsimp at hom_inv_id, dsimp,
      rw ← category_theory.comp_apply,
      rw hom_inv_id, refl },
    rw (_ : this.hom (submodule.quotient.mk c') = 0) at is_zero,
    { simp at is_zero,
      symmetry' at is_zero,
      rw submodule.quotient.mk_eq_zero at is_zero,
      exact is_zero },
    { rw ← H,
      delta Module.to_homology,
      rw h,
      transitivity (Module.as_hom_left (submodule.mkq (linear_map.range (C.boundaries_to_cycles j))) ≫ this.hom) c',
      refl,
      apply congr_fun,
      transitivity (homology.π (C.d_to j) (C.d_from j) _ : C.cycles j → cokernel (C.boundaries_to_cycles j)),
      apply congr_arg,
      apply Module.range_mkq_cokernel_iso_range_quotient_inv,
      refl } },
  cases this with y' h,
  delta homological_complex.boundaries at y',
  delta image_subobject at y',
  destruct (Module.image_iso_range (C.d_to j)).hom
              ((image_subobject_iso (C.d_to j)).hom y'),
  intros y hy hy',
  let y'' : linear_map.ker (C.d_from j) := set.inclusion _ ⟨y, hy⟩,
  swap,
  { intros z hz, cases hz with z' hz, rw ← hz,
    change (C.d_to j ≫ C.d_from j) z' = 0, simp },
  cases hy with w hw,
  existsi (C.X_prev_iso hij).hom w,
  rw C.d_to_eq hij at hw,
  transitivity y, assumption,
  suffices : Module.to_cycles ⟨x, is_cycle⟩ = Module.to_cycles y'',
  { symmetry,
    replace this := congr_arg ⇑(kernel_subobject (C.d_from j)).arrow this,
    rw [Module.to_kernel_subobject_arrow, Module.to_kernel_subobject_arrow] at this,
    exact this },
  rw ← h,
  apply Module.cycles_ext,
  simp,
  have := congr_arg subtype.val hy',
  simp at this, 
  rw ← this,
  transitivity ((image_subobject_iso (C.d_to j)).hom
                ≫ (Module.image_iso_range (C.d_to j)).hom
                ≫ (submodule.subtype (linear_map.range (C.d_to j)))) y',
  { congr,
    rw (_ : (linear_map.range (C.d_to j)).subtype
          = Module.of_hom ((linear_map.range (C.d_to j)).subtype)),
    rw ← Module.image_iso_range_inv_image_ι (C.d_to j),
    rw ← category.assoc (iso.hom _) (iso.inv _) _,
    rw iso.hom_inv_id, simp, refl },
  refl
end

noncomputable
def preim_cycle_of_to_homology_zero {ι : Type w} {c : complex_shape ι}
                                    (C : homological_complex (Module.{vhom} R) c) (i j : ι)
                                    (hij : c.rel i j)
                                    (x : C.X j) (is_cycle : C.d_from j x = 0)
                                    (H : Module.to_homology ⟨x, is_cycle⟩ = 0) : C.X i :=
@classical.some (C.X i) (λ y, C.d i j y = x)
                (exists_preim_cycle_of_to_homology_zero C i j hij x is_cycle H)

lemma preim_cycle_of_to_homology_zero_spec {ι : Type w} {c : complex_shape ι}
                                           (C : homological_complex (Module.{vhom} R) c) (i j : ι)
                                           (hij : c.rel i j)
                                           (x : C.X j) (is_cycle : C.d_from j x = 0)
                                           (H : Module.to_homology ⟨x, is_cycle⟩ = 0)
    : (C.d i j) (preim_cycle_of_to_homology_zero C i j hij x is_cycle H) = x :=
@classical.some_spec (C.X i) (λ y, C.d i j y = x)
                     (exists_preim_cycle_of_to_homology_zero C i j hij x is_cycle H)

noncomputable
def preim_cycle_of_homology_zero {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module.{vhom} R) c) (i j : ι)
                                 (hij : c.rel i j)
                                 (H : is_isomorphic (C.homology j) 0)
                                 (x : C.X j) (is_cycle : C.d_from j x = 0) : C.X i :=
preim_cycle_of_to_homology_zero C i j hij x is_cycle (all_eq_zero_of_iso_zero H _)

lemma preim_cycle_of_homology_zero_spec {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module.{vhom} R) c) (i j : ι)
                                 (hij : c.rel i j)
                                 (H : is_isomorphic (C.homology j) 0)
                                 (x : C.X j) (is_cycle : C.d_from j x = 0)
  : C.d i j (preim_cycle_of_homology_zero C i j hij H x is_cycle) = x :=
preim_cycle_of_to_homology_zero_spec C i j hij x is_cycle (all_eq_zero_of_iso_zero H _)

lemma exists_preim_homology_class {ι : Type w} {c : complex_shape ι}
                                  (C : homological_complex (Module.{vhom} R) c) (i : ι)
                                  (y : C.homology i)
  : ∃ (x : C.X i) (h : C.d_from i x = 0), Module.to_homology ⟨x, h⟩ = y :=
let s := (linear_map.range (image_to_kernel (C.d_to i) (C.d_from i) (by simp))).quotient_rel in
begin
  generalize h : (Module.cokernel_iso_range_quotient _).hom y = y',
  have h' : (Module.cokernel_iso_range_quotient _).inv y' = y,
  { rw ← h,
    transitivity ((Module.cokernel_iso_range_quotient _).hom
                 ≫ (Module.cokernel_iso_range_quotient _).inv) y,
    refl,
    rw iso.hom_inv_id, refl },
  rw ← h', clear h' h y,
  induction y' with x',
  { existsi (kernel_subobject (C.d_from i)).arrow x',
    have : C.d_from i ((kernel_subobject (C.d_from i)).arrow x') = 0, simp,
    existsi this,
    suffices h : (Module.cokernel_iso_range_quotient (image_to_kernel (C.d_to i) (C.d_from i) _)).hom
               (Module.to_homology ⟨(kernel_subobject (C.d_from i)).arrow x', this⟩)
               = quot.mk (@setoid.r _ s) x',
    { have : ((Module.cokernel_iso_range_quotient (image_to_kernel (C.d_to i) (C.d_from i) _)).hom 
             ≫ (Module.cokernel_iso_range_quotient (image_to_kernel (C.d_to i) (C.d_from i) _)).inv)
             (Module.to_homology ⟨(kernel_subobject (C.d_from i)).arrow x', this⟩)
           = (Module.cokernel_iso_range_quotient (image_to_kernel (C.d_to i) (C.d_from i) _)).inv
             (quot.mk (@setoid.r _ s) x')
       := congr_arg (Module.cokernel_iso_range_quotient (image_to_kernel (C.d_to i) (C.d_from i) _)).inv h,
      rw iso.hom_inv_id at this,
      exact this },
    delta Module.to_homology, delta homology.π,
    simp,
    congr, ext, simp },
  { refl }
end

noncomputable
def preim_of_homology_class {ι : Type w} {c : complex_shape ι}
                            (C : homological_complex (Module.{vhom} R) c) (i : ι)
                            (y : C.homology i) : C.X i :=
  classical.some (exists_preim_homology_class C i y)

def preim_of_homology_class_spec {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module.{vhom} R) c) (i : ι)
                                 (y : C.homology i)
  : ∃ (h : C.d_from i (preim_of_homology_class C i y) = 0),
      Module.to_homology ⟨preim_of_homology_class C i y, h⟩ = y :=
  classical.some_spec (exists_preim_homology_class C i y)

end

def chain_complex.mk_nat_trans_rec {C : Type*} [category C] {V : Type*} [category V] [abelian V]
  {F G : C ⥤ chain_complex V ℕ}
  (init : (F ⋙ homological_complex.eval V _ 0) ⟶ (G ⋙ homological_complex.eval V _ 0))
  (step : Π (n : ℕ) (η : (F ⋙ homological_complex.eval V _ n)
                       ⟶ (G ⋙ homological_complex.eval V _ n)),
            (∀ X, (F.obj X).d (n + 1) n ≫ nat_trans.app η X ≫ (G.obj X).d_from n = 0)
            → ((F ⋙ homological_complex.eval V _ (n + 1))
              ⟶ (G ⋙ homological_complex.eval V _ (n + 1))))
  (Hstep : ∀ (n : ℕ) (η : (F ⋙ homological_complex.eval V _ n)
                       ⟶ (G ⋙ homological_complex.eval V _ n))
             (h : ∀ X, (F.obj X).d (n + 1) n ≫ nat_trans.app η X ≫ (G.obj X).d_from n = 0),
             ∀ X, nat_trans.app (step n η h) X ≫ (G.obj X).d (n + 1) n
                = (F.obj X).d (n + 1) n ≫ nat_trans.app η X)
  : F ⟶ G :=
  homological_complex.mk_nat_trans
    (λ k,
      (@nat.rec (λ n, Σ' (η : (F ⋙ homological_complex.eval V _ n)
                            ⟶ (G ⋙ homological_complex.eval V _ n)), 
                        ∀ X, (F.obj X).d_to n ≫ nat_trans.app η X ≫ (G.obj X).d_from n = 0)
                ⟨init, by simp⟩
                (λ n p, have ∀ X, (F.obj X).d (n + 1) n ≫ p.fst.app X
                                ≫ homological_complex.d_from (G.obj X) n = 0,
                        by { intro X, have := p.2 X,
                             rw homological_complex.d_to_eq _ (complex_shape.down_mk (n + 1) n rfl) at this,
                             rw category.assoc at this,
                             rw ← category_theory.iso.eq_inv_comp at this,
                             simp at this, exact this },
                        ⟨step n p.1 this,
                         by { intro X,
                              rw homological_complex.d_from_eq _ (complex_shape.down_mk (n + 1) n rfl),
                              rw ← category.assoc ((step n p.fst this).app X),
                              rw Hstep,
                              rw [← category.assoc, ← category.assoc],
                              rw homological_complex.d_to_eq _ (complex_shape.down_mk (n + 2) (n + 1) rfl),
                              simp }⟩)
                k).fst)
    (by { intros i j h X, dsimp at h, subst h, apply Hstep })

def chain_complex.mk_natural_chain_homotopy {C : Type*} [category C]
  {V : Type*} [category V] [abelian V]
  {F G : C ⥤ chain_complex V ℕ}
  {α β : F ⟶ G}
  (s : Π n, (F ⋙ homological_complex.eval V _ n) ⟶ (G ⋙ homological_complex.eval V _ (n + 1)))
  (diff_eq_sd_plus_ds_deg0 : ∀ X, (nat_trans.app α X).f 0 = ((s 0).app X ≫ (G.obj X).d 1 0) + (nat_trans.app β X).f 0)
  (diff_eq_sd_plus_ds : ∀ n X, (nat_trans.app α X).f (n + 1)
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
                                         { simp, exact diff_eq_sd_plus_ds_deg0 X },
                                         { simp, exact diff_eq_sd_plus_ds n X } } },
    naturality := λ X Y f i j h, by { dsimp at h, subst h, simp, exact (s j).naturality' f } 
  }

def chain_complex.mk_natural_chain_homotopy_rec {C : Type*} [category C]
  {V : Type*} [category V] [abelian V]
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

section

local attribute [instance] category_theory.limits.has_zero_object.has_zero

universes u' uhom' v' vmod' w'

parameters {C : Type u'} [category.{uhom'} C] {R : Type v'} [comm_ring R] 

structure functor_basis (F : C ⥤ (Module.{vmod'} R)) : Type (max u' uhom' v' (vmod' + 1) w' + 1) :=
(indices : Type w')
(models : indices → C)
(basis_elem : Π (i : indices), F.obj (models i))
(lin_indep : ∀ (X : C), linear_independent R (λ p : (Σ (i : indices), models i ⟶ X),
                                                F.map p.snd (basis_elem p.fst)))
(spanning : ∀ (X : C), submodule.span R { x | ∃ (i : indices) (f : models i ⟶ X), F.map f (basis_elem i) = x } = ⊤)

noncomputable
def functor_basis.get_basis {F : C ⥤ Module.{vmod'} R} (b : functor_basis F) (X : C)
  : basis (Σ (i : b.indices), b.models i ⟶ X) R (F.obj X) :=
basis.mk (b.lin_indep X) (by { rw ← b.spanning X, congr, ext, simp })

noncomputable
def functor_basis.map_out {F : C ⥤ Module.{vmod'} R} (b : functor_basis F) (G : functor C (Module.{vmod'} R))
  (choices : Π (i : b.indices), G.obj (b.models i)) : F ⟶ G := {
    app := λ X, basis.constr (b.get_basis X) R (λ p, G.map p.2 (choices p.1)),
    naturality' := by { 
      intros X Y f,
      apply basis.ext (b.get_basis X),
      intro p, cases p with i g,
      simp only [basis.constr_basis,
                 homological_complex.eval_map,
                 category_theory.functor.comp_map,
                 function.comp_app,
                 Module.coe_comp], 
      rw (_ : G.map f (G.map g _) = (G.map g ≫ G.map f) _), swap, refl,
      rw ← G.map_comp,
      have : F.map f (b.get_basis X ⟨i, g⟩) = b.get_basis Y ⟨i, g ≫ f⟩,
      { dsimp [functor_basis.get_basis],
        rw [basis.mk_apply, basis.mk_apply],
        simp },
      rw this,
      apply basis.constr_basis
     }
  }

lemma map_out_desc {F : C ⥤ Module.{vmod'} R} (b : functor_basis F) (G : C ⥤ Module.{vmod'} R)
  (choices : Π (i : b.indices), G.obj (b.models i))
  {X : C} (i : b.indices) (f : b.models i ⟶ X)
  : ((b.map_out G choices).app X (b.get_basis X ⟨i, f⟩))
  = G.map f (choices i) :=
basis.constr_basis (b.get_basis X) R (λ p, G.map p.2 (choices p.1)) ⟨i, f⟩

def complex_functor_basis (F : C ⥤ chain_complex (Module.{vmod'} R) ℕ) :=
  Π (n : ℕ), functor_basis (F ⋙ homological_complex.eval _ _ n)

-- dieck says it should be H_{n+1}(G_*(B_{n+1, j})) = 0 but it's actually
-- H_{n+1}(G_*(B_{n, j})) = 0 and H_n(G_*(B_{n, j})) = 0
def acyclic {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
            (G : C ⥤ (chain_complex (Module.{vmod'} R) ℕ)) := 
  ∀ n (i : (b (n + 1)).indices), is_isomorphic ((G.obj ((b (n+1)).models i)).homology n) 0
                               ∧ is_isomorphic ((G.obj ((b (n+1)).models i)).homology (n + 1)) 0

noncomputable
def lift_nat_trans_deg0 {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                        (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
  (H_acyclic : acyclic b G)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 0) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 0)
                (λ i, preim_of_homology_class (G.obj ((b 0).models i))
                                              0
                                              (ϕ.app ((b 0).models i)
                                                     (Module.to_homology ⟨(b 0).basis_elem i,
                                                                          by simp⟩)))

noncomputable
def lift_nat_trans_step {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                        (G : functor C (chain_complex (Module.{vmod'} R) ℕ))
                        (H_acyclic : acyclic b G) (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i : (b (n + 1)).indices, ψ.app ((b (n + 1)).models i) ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
                                ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  : (F ⋙ homological_complex.eval _ _ (n + 1)) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)) := 
  (b (n + 1)).map_out (G ⋙ homological_complex.eval _ _ (n + 1))
                      (λ i, 
  let F'  := F ⋙ homological_complex.eval _ _ (n + 1),
      m   := (b (n + 1)).models i,
      b_m := (b (n + 1)).basis_elem i in
  preim_cycle_of_homology_zero _ _ _
                               (rfl : (complex_shape.down ℕ).rel (n + 1) n)
                               (H_acyclic n i).left
                               _
                               (H i))

lemma step_chain_map {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                     (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                     (H_acyclic : acyclic b G) (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i : (b (n + 1)).indices, ψ.app ((b (n + 1)).models i) ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
                                ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  (X : C)
  : (lift_nat_trans_step b G H_acyclic n ψ H).app X ≫ (G.obj X).d (n + 1) n
  = (F.obj X).d (n + 1) n ≫ ψ.app X :=
begin
  apply basis.ext ((b (n + 1)).get_basis X),
  intro p, cases p with i f,
  dsimp [lift_nat_trans_step],
  rw map_out_desc,
  rw [category_theory.functor.comp_map, homological_complex.eval_map],
  rw ← category_theory.comp_apply ((G.map f).f (n + 1)) ((G.obj X).d (n + 1) n),
  rw (G.map f).comm' _ _ (complex_shape.down_mk (n + 1) n rfl),
  rw category_theory.comp_apply,
  rw preim_cycle_of_homology_zero_spec,
  rw ← category_theory.comp_apply _ ((G.map f).f n),
  have := ψ.naturality' f,
  dsimp at this, rw ← this,
  rw category_theory.comp_apply,
  congr,
  rw [← category_theory.comp_apply, ← (F.map f).comm' _ _ (complex_shape.down_mk (n + 1) n rfl)],
  dsimp [functor_basis.get_basis],
  rw basis.mk_apply
end

noncomputable
def lift_nat_trans {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                   (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                   (H_acyclic : acyclic b G)
                   (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                      ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : F ⟶ G :=
  have ∀ (n : ℕ) (η : F ⋙ homological_complex.eval _ _ n ⟶ G ⋙ homological_complex.eval _ _ n)
         (h : ∀ (X : C), (F.obj X).d (n + 1) n ≫ nat_trans.app η X
                         ≫ homological_complex.d_from (G.obj X) n = 0)
         (i : (b (n + 1)).indices),
         nat_trans.app η ((b (n + 1)).models i) ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
         ∈ linear_map.ker (homological_complex.d_from (G.obj ((b (n + 1)).models i)) n)
  := λ n η h i, congr_fun (congr_arg coe_fn (h ((b (n + 1)).models i))) ((b (n + 1)).basis_elem i),
  chain_complex.mk_nat_trans_rec (lift_nat_trans_deg0 b G H_acyclic ϕ)
                                 (λ n η h, lift_nat_trans_step b G H_acyclic n η (this n η h))
                                 (λ n η h, step_chain_map b G H_acyclic n η (this n η h))

lemma lift_nat_trans_app0 {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
  (H_acyclic : acyclic b G) (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  (X : C) (i : (b 0).indices) (f : (b 0).models i ⟶ X)
  (h : (G.obj X).d_from 0 (((lift_nat_trans b G H_acyclic ϕ).app X).f 0 ((b 0).get_basis X ⟨i, f⟩)) = 0)
  : Module.to_homology ⟨((lift_nat_trans b G H_acyclic ϕ).app X).f 0 ((b 0).get_basis X ⟨i, f⟩), h⟩
  = (G ⋙ homology_functor (Module R) _ 0).map f
      (ϕ.app ((b 0).models i) (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩)) := 
begin
  transitivity Module.to_homology ⟨(lift_nat_trans_deg0 b G H_acyclic ϕ).app X ((b 0).get_basis X ⟨i, f⟩), by simp⟩,
  refl,
  dsimp [lift_nat_trans_deg0],
  rw map_out_desc,
  transitivity (G ⋙ homology_functor (Module R) _ 0).map f
                (Module.to_homology ⟨preim_of_homology_class (G.obj ((b 0).models i)) 0
                  (ϕ.app ((b 0).models i)
                         (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩)), by simp⟩),
  { simp only [homology.π_map_apply,
               category_theory.functor.comp_map,
               homology_functor_map,
               homological_complex.eval_map],
    delta Module.to_homology,
    congr,
    symmetry,
    transitivity (cycles_map (G.map f) 0) (Module.to_cycles _), refl,
    rw Module.cycles_map_to_cycles },
  { cases (preim_of_homology_class_spec (G.obj ((b 0).models i)) 0
                                      (ϕ.app ((b 0).models i)
                                        (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩)))
        with h' H,
    congr,
    exact H },
end

lemma lift_nat_trans_spec {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                          (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                          (H_acyclic : acyclic b G)
                          (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                             ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : whisker_right (lift_nat_trans b G H_acyclic ϕ) (homology_functor (Module R) _ 0) = ϕ := 
begin
  ext X : 2,
  apply homology.ext,
  have : kernel_subobject (homological_complex.d_from (F.obj X) 0) = ⊤, simp, 
  rw ← category_theory.subobject.is_iso_iff_mk_eq_top at this,
  let f : kernel (homological_complex.d_from (F.obj X) 0)
        ≅ (F.obj X).X 0 := @category_theory.as_iso _ _ _ _ _ this,
  let f' : ↑ (kernel_subobject (homological_complex.d_from (F.obj X) 0))
        ≅ (F.obj X).X 0,
  { transitivity,
    apply category_theory.subobject.underlying_iso,
    exact f },
  refine (category_theory.iso.cancel_iso_hom_left f'.symm _ _).mp _,
  apply basis.ext ((b 0).get_basis X),
  intro p, cases p with i f,
  simp only [category_theory.whisker_right_app,
            category_theory.iso.trans_symm,
            category_theory.as_iso_inv,
            function.comp_app,
            category_theory.iso.symm_hom,
            category_theory.category.assoc,
            Module.coe_comp,
            category_theory.iso.trans_hom],
  transitivity (ϕ.app X) (Module.to_homology ⟨(b 0).get_basis X ⟨i, f⟩, (by simp)⟩),
  { transitivity (homology_functor (Module R) (complex_shape.down ℕ) 0).map ((lift_nat_trans b G H_acyclic ϕ).app X)
                  (Module.to_homology ⟨(b 0).get_basis X ⟨i, f⟩, (by simp)⟩),
    { congr, symmetry, 
      apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ this),
      simp },
    { dsimp [homology_functor],
      simp,
      rw (_ : (kernel_subobject_map (homological_complex.hom.sq_from ((lift_nat_trans b G H_acyclic ϕ).app X) 0))
            = cycles_map ((lift_nat_trans b G H_acyclic ϕ).app X) 0),
      rw Module.cycles_map_to_cycles,
      dsimp [subtype.val],
      transitivity, apply lift_nat_trans_app0,
      rw [← category_theory.comp_apply (ϕ.app ((b 0).models i)) _],
      rw ← ϕ.naturality,
      refine congr_arg (coe_fn (ϕ.app X)) _,
      simp, delta Module.to_homology,
      congr,
      transitivity, apply Module.cycles_map_to_cycles,
      apply congr_arg Module.to_cycles,
      congr, symmetry, apply basis.mk_apply,
      refl } },
  { apply congr_arg,
    delta Module.to_homology,
    delta Module.to_cycles,
    congr,
    simp,
    rw [← category_theory.comp_apply],
    transitivity ((subobject.underlying_iso (kernel.ι (homological_complex.d_from (F.obj X) 0)))
                  ≪≫ (@category_theory.as_iso _ _ _ _ _ this)).inv
                    (((F ⋙ homological_complex.eval (Module R) _ 0).map f) ((b 0).basis_elem i)),
    { apply category_theory.eq_app_inv_of_app_hom_eq
              ((subobject.underlying_iso (kernel.ι (homological_complex.d_from (F.obj X) 0)))
                ≪≫ (@category_theory.as_iso _ _ _ _ _ this)),
      simp,
      apply basis.mk_apply },
    simp, congr, symmetry, apply basis.mk_apply }
end

noncomputable
def chain_htpy_of_lifts_deg0 {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                             (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                             (H_acyclic : acyclic b G)
                             (α β : F ⟶ G)
                             (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                                             = whisker_right β (homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 1)
                (λ i, preim_cycle_of_to_homology_zero (G.obj ((b 0).models i)) 1 0 rfl
                                                      (((α - β).app ((b 0).models i)).f 0 ((b 0).basis_elem i))
                                                      (by simp)
                                                      (by { 
    have h1 : (α.app ((b 0).models i)).f 0 ((b 0).basis_elem i)
            ∈ linear_map.ker (homological_complex.d_from (G.obj ((b 0).models i)) 0),
    { simp },
    have h2 : (β.app ((b 0).models i)).f 0 ((b 0).basis_elem i)
            ∈ linear_map.ker (homological_complex.d_from (G.obj ((b 0).models i)) 0),
    { simp },
    generalize c1_def : (⟨(α.app ((b 0).models i)).f 0 ((b 0).basis_elem i), h1⟩
                        : linear_map.ker (homological_complex.d_from (G.obj ((b 0).models i)) 0))
                      = c1,
    generalize c2_def : (⟨(β.app ((b 0).models i)).f 0 ((b 0).basis_elem i), h2⟩
                        : linear_map.ker (homological_complex.d_from (G.obj ((b 0).models i)) 0))
                      = c2,
    transitivity @has_sub.sub (@homological_complex.homology ℕ (Module R) _ _ (complex_shape.down ℕ) _ _ _ _
                                (G.obj ((b 0).models i)) 0) 
                        (by apply_instance)
                        (Module.to_homology c1)
                        (Module.to_homology c2),
    { transitivity Module.to_homology (c1 - c2),
      congr, rw [← c1_def, ← c2_def], simp,  
      exact is_linear_map.map_sub (Module.to_homology.homomorphism (G.obj ((b 0).models i)) _) c1 c2 },
    { rw sub_eq_zero,
      rw [← c1_def, ← c2_def],
      have :=  congr_fun
                (congr_arg coe_fn
                  (congr_fun
                    (congr_arg nat_trans.app same_map_on_H0)
                    ((b 0).models i)))
                (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩),
      simp at this,
      rw [(_ : kernel_subobject_map (homological_complex.hom.sq_from (α.app ((b 0).models i)) 0)
             = cycles_map (α.app ((b 0).models i)) 0),
          (_ : kernel_subobject_map (homological_complex.hom.sq_from (β.app ((b 0).models i)) 0)
             = cycles_map (β.app ((b 0).models i)) 0),
          Module.cycles_map_to_cycles,
          Module.cycles_map_to_cycles] at this,
      exact this,
      refl, refl }}))

lemma chain_htpy_of_lifts_deg0_chain_htpy
  {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  (X : C)
  : (α.app X).f 0 = ((chain_htpy_of_lifts_deg0 b G H_acyclic α β same_map_on_H0).app X ≫ (G.obj X).d 1 0) + (β.app X).f 0 :=
begin
  apply basis.ext ((b 0).get_basis X),
  intro p, cases p with i f,
  simp [chain_htpy_of_lifts_deg0],
  rw map_out_desc,
  simp,
  rw ← category_theory.comp_apply,
  rw (G.map f).comm,
  simp,
  rw preim_cycle_of_to_homology_zero_spec,
  simp,
  dsimp [functor_basis.get_basis],
  rw basis.mk_apply,
  dsimp [psigma.snd],
  rw [← category_theory.comp_apply _ ((β.app _).f 0), ← homological_complex.comp_f, β.naturality],
  rw sub_add,
  simp,
  rw [← category_theory.comp_apply, ← homological_complex.comp_f, α.naturality],
  refl
end

noncomputable
def chain_htpy_of_lifts_step {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                             (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                             (H_acyclic : acyclic b G)
                             (α β : F ⟶ G)
                             (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                                             = whisker_right β (homology_functor (Module R) _ 0))
  (n : ℕ)
  (s : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)))
  (H : ∀ X, ((α.app X).f (n + 1)) ≫ (G.obj X).d (n + 1) n
            = (((F.obj X).d (n + 1) n ≫ nat_trans.app s X) + (β.app X).f (n + 1))
              ≫ (G.obj X).d (n + 1) n)
  : (F ⋙ homological_complex.eval _ _ (n + 1)) ⟶ (G ⋙ homological_complex.eval _ _ (n + 2)) :=
  (b (n + 1)).map_out (G ⋙ homological_complex.eval _ _ (n + 2))
                      (λ i, preim_cycle_of_homology_zero (G.obj ((b (n + 1)).models i)) (n + 2) (n + 1) rfl
                                                         (H_acyclic n i).right
                                                         ((whisker_right α (homological_complex.eval (Module R) _ (n + 1))
                                                           - whisker_right β (homological_complex.eval (Module R) _ (n + 1))
                                                           - (homological_complex.d_nat_trans F (n + 1) n ≫ s)).app
                                                          ((b (n + 1)).models i) ((b (n + 1)).basis_elem i))
                                                         (by { rw homological_complex.d_from_eq _ (complex_shape.down_mk (n + 1) n rfl),
                                                               rw category_theory.comp_apply,
                                                               transitivity (homological_complex.X_next_iso (G.obj ((b (n + 1)).models i)) _).inv 0,
                                                               apply congr_arg,
                                                               { have := congr_fun (congr_arg coe_fn (H ((b (n + 1)).models i))) ((b (n + 1)).basis_elem i),
                                                                 rw [category_theory.comp_apply, category_theory.comp_apply] at this,
                                                                 rw ← sub_eq_zero at this,
                                                                 rw ← map_sub ((G.obj ((b (n + 1)).models i)).d (n + 1) n) at this,
                                                                 refine eq.trans _ this,
                                                                 congr,
                                                                 simp, rw sub_add_eq_sub_sub_swap,
                                                                 refl },
                                                               simp }))

lemma chain_htpy_of_lifts_step_chain_htpy
  {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  (n : ℕ)
  (s : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)))
  (h : ∀ X, ((α.app X).f (n + 1)) ≫ (G.obj X).d (n + 1) n
            = (((F.obj X).d (n + 1) n ≫ nat_trans.app s X) + (β.app X).f (n + 1))
              ≫ (G.obj X).d (n + 1) n)
  : ∀ X, (nat_trans.app α X).f (n + 1)
          = ((F.obj X).d (n + 1) n ≫ s.app X)
          + ((chain_htpy_of_lifts_step b G H_acyclic α β same_map_on_H0 n s h).app X ≫ (G.obj X).d (n + 2) (n + 1))
          + (nat_trans.app β X).f (n + 1) :=
begin
  intro X,
  apply basis.ext ((b (n + 1)).get_basis X),
  intro p, cases p with i f,
  dsimp [chain_htpy_of_lifts_step],
  rw map_out_desc,
  dsimp,
  rw [← category_theory.comp_apply ((G.map f).f (n + 2)), (G.map f).comm],
  dsimp,
  rw preim_cycle_of_homology_zero_spec,
  simp [homological_complex.d_nat_trans,
        functor_basis.get_basis, basis.mk_apply],
  have : ∀ a b c d e f : (G.obj X).X (n + 1),
        (a = c) → (b = e) → (f = d) → a = (b + (c - d - e)) + f,
  { intros a b c d e f h1 h2 h3, subst h1, subst h2, subst h3, simp },
  apply this;
  try { rw [← category_theory.comp_apply, ← homological_complex.comp_f, nat_trans.naturality], refl },
  rw ← category_theory.comp_apply ((F.map f).f (n + 1)),
  rw (F.map f).comm,
  dsimp, 
  rw [← category_theory.comp_apply, 
      (_ : (F.map f).f n = (F ⋙ homological_complex.eval _ _ n).map f),
      nat_trans.naturality],
  refl,
  refl
end


noncomputable
def lift_nat_trans_unique {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
                          (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
                          (H_acyclic : acyclic b G)
                          (α β : F ⟶ G)
                          (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                                          = whisker_right β (homology_functor (Module R) _ 0))
  : natural_chain_homotopy α β := 
  let x := chain_htpy_of_lifts_step b G H_acyclic α β same_map_on_H0,
      y := chain_htpy_of_lifts_step_chain_htpy b G H_acyclic α β same_map_on_H0 in
  chain_complex.mk_natural_chain_homotopy_rec
            (chain_htpy_of_lifts_deg0 b G H_acyclic α β same_map_on_H0) 
            (chain_htpy_of_lifts_deg0_chain_htpy b G H_acyclic α β same_map_on_H0)
            x
            y

-- should be a lemma but I get weird errors if I do?
lemma lifts_of_nat_trans_H0_give_same_map_in_homology 
  {F : C ⥤ chain_complex (Module.{vmod'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vmod'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  (n : ℕ) (X : C)
  : (whisker_right α (homology_functor (Module R) _ n)).app X
  = (whisker_right β (homology_functor (Module R) _ n)).app X :=
  homology_map_eq_of_homotopy
    (natural_chain_homotopy.to_chain_htpy
      (lift_nat_trans_unique b G H_acyclic α β same_map_on_H0) X)
    n

end

