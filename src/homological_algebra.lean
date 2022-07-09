import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy

open category_theory category_theory.limits

-- I do not understand universes

section

local attribute [instance] category_theory.limits.has_zero_object.has_zero
local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

universes u v w

parameters {C : Type u} [category C] {R : Type v} [comm_ring R]

lemma category_theory.eq_app_inv_of_app_hom_eq [concrete_category C] {X Y : C} (f : X ≅ Y)
  {x : X} {y : Y} (H : f.hom x = y) : x = f.inv y := 
begin
  transitivity f.inv (f.hom x),
  { simp },
  { rw H }
end

def homological_complex.mk_nat_trans {V : Type v} [category V] [abelian V]
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

instance zero_obj_subsingleton : subsingleton (0 : Module R) := 
  let f := is_zero.iso_zero (Module.is_zero_of_subsingleton (Module.of R punit))
  in ⟨λ a b, have h : f.hom (f.inv a) = f.hom (f.inv b),
             from congr_arg f.hom (subsingleton.elim (f.inv a) (f.inv b)),
             by { change (f.inv ≫ f.hom) a = (f.inv ≫ f.hom) b at h,
                  rw iso.inv_hom_id at h, exact h }⟩ 

def exists_preim_cycle_of_homology_zero {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module R) c) (i j : ι)
                                 (hij : c.rel i j)
                                 (H : is_isomorphic (C.homology j) 0)
                                 (x : C.X j) (is_cycle : C.d_from j x = 0)
  : ∃ x_1 : C.X i, (C.d i j) x_1 = x :=
begin
  have : function.surjective (C.boundaries_to_cycles j),
  { have H' := H, 
    delta homological_complex.homology at H',
    delta homology at H',
    cases H',
    have := (Module.cokernel_iso_range_quotient _).symm.trans H',
    intro c,
    delta homological_complex.cycles at c,
    have is_zero : this.inv (this.hom (submodule.quotient.mk c_1))
                  = submodule.quotient.mk c_1,
    { transitivity (this.hom ≫ this.inv) (submodule.quotient.mk c_1), refl,
      have hom_iv_eq_id := this.hom_inv_id',
      dsimp at hom_iv_eq_id, rw hom_iv_eq_id, refl },
    rw (_ : this.hom (submodule.quotient.mk c_1) = 0) at is_zero,
    { simp at is_zero,
      symmetry' at is_zero,
      rw submodule.quotient.mk_eq_zero at is_zero,
      exact is_zero },
    { apply subsingleton.elim } },
  let x' := Module.to_cycles ⟨x, is_cycle⟩,
  cases (this x') with y' h,
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
  change (x' = Module.to_cycles y''),
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
def preim_cycle_of_homology_zero {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module R) c) (i j : ι)
                                 (hij : c.rel i j)
                                 (H : is_isomorphic (C.homology j) 0)
                                 (x : C.X j) (is_cycle : C.d_from j x = 0) : C.X i :=
@classical.some (C.X i) (λ y, C.d i j y = x)
                (exists_preim_cycle_of_homology_zero C i j hij H x is_cycle)

lemma preim_cycle_of_homology_zero_spec {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module R) c) (i j : ι)
                                 (hij : c.rel i j)
                                 (H : is_isomorphic (C.homology j) 0)
                                 (x : C.X j) (is_cycle : C.d_from j x = 0)
  : C.d i j (preim_cycle_of_homology_zero C i j hij H x is_cycle) = x :=
@classical.some_spec (C.X i) (λ y, C.d i j y = x)
                     (exists_preim_cycle_of_homology_zero C i j hij H x is_cycle)

lemma exists_preim_homology_class {ι : Type w} {c : complex_shape ι}
                                  (C : homological_complex (Module R) c) (i : ι)
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
    simp, --[Module.cokernel_π_cokernel_iso_range_quotient_hom],
    congr, ext, simp },
  { refl }
end

noncomputable
def preim_of_homology_class {ι : Type w} {c : complex_shape ι}
                            (C : homological_complex (Module R) c) (i : ι)
                            (y : C.homology i) : C.X i :=
  classical.some (exists_preim_homology_class C i y)

def preim_of_homology_class_spec {ι : Type w} {c : complex_shape ι}
                                 (C : homological_complex (Module R) c) (i : ι)
                                 (y : C.homology i)
  : ∃ (h : C.d_from i (preim_of_homology_class C i y) = 0),
      Module.to_homology ⟨preim_of_homology_class C i y, h⟩ = y :=
  classical.some_spec (exists_preim_homology_class C i y)

end

section

local attribute [instance] category_theory.limits.has_zero_object.has_zero

universes u' v' w'

parameters {C : Type u'} [category C] {R : Type v'} [comm_ring R] 

structure based_free_functor :=
(F : functor C (Module R))
(indices : Type w')
(models : indices → C)
(basis : Π (i : indices), F.obj (models i))
(lin_indep : ∀ (X : C), linear_independent R (λ p : (Σ (i : indices), models i ⟶ X),
                                                F.map p.snd (basis p.fst)))
(spanning : ∀ (X : C), submodule.span R { x | ∃ (i : indices) (f : models i ⟶ X), F.map f (basis i) = x } = ⊤)

noncomputable
def based_free_functor.get_basis (F : based_free_functor) (X : C)
  : basis (Σ (i : F.indices), F.models i ⟶ X) R
          (F.F.obj X) :=
basis.mk (F.lin_indep X) (by { rw ← F.spanning X, congr, ext, simp })

noncomputable
def based_free_functor.map_out (F : based_free_functor) (G : functor C (Module R))
  (choices : Π (i : F.indices), G.obj (F.models i)) : F.F ⟶ G := {
    app := λ X, basis.constr (F.get_basis X) R (λ p, G.map p.2 (choices p.1)),
    naturality' := by { 
      intros X Y f,
      apply basis.ext (F.get_basis X),
      intro p, cases p with i g,
      simp only [basis.constr_basis,
                 homological_complex.eval_map,
                 category_theory.functor.comp_map,
                 function.comp_app,
                 Module.coe_comp], 
      rw (_ : G.map f (G.map g _) = (G.map g ≫ G.map f) _), swap, refl,
      rw ← G.map_comp,
      have : F.F.map f (F.get_basis X ⟨i, g⟩) = F.get_basis Y ⟨i, g ≫ f⟩,
      { dsimp [based_free_functor.get_basis],
        rw [basis.mk_apply, basis.mk_apply],
        simp },
      rw this,
      apply basis.constr_basis
     }
  }

lemma map_out_desc  (F : based_free_functor) (G : functor C (Module R))
  (choices : Π (i : F.indices), G.obj (F.models i))
  {X : C} (i : F.indices) (f : F.models i ⟶ X)
  : ((based_free_functor.map_out F G choices).app X (F.F.map f (F.basis i)))
  = G.map f (choices i) :=
  by { have :=  basis.constr_basis (F.get_basis X) R (λ p, G.map p.2 (choices p.1)) ⟨i, f⟩,
       dsimp at this,
       dsimp [based_free_functor.map_out],
       rw ← this, congr,
       symmetry,
       apply basis.mk_apply }

-- Should probably generalize ℕ to ι
structure based_complex_functor := 
(in_degree : ℕ → based_free_functor)
(differentials : Π n, (in_degree (n + 1)).F ⟶ (in_degree n).F)
(dd_eq_zero : Π n, differentials (n + 1) ≫ differentials n = 0)

def based_complex_functor.to_complex_functor (F : based_complex_functor)
  : functor C (chain_complex (Module R) ℕ) := {
    obj := λ X, chain_complex.of (λ n, (F.in_degree n).F.obj X)
                                 (λ n, (F.differentials n).app X)
                                 (λ n, eq.trans (nat_trans.comp_app _ _ X).symm
                                                (by rw F.dd_eq_zero n; refl)),
    map := λ X Y f, {
      f := λ n, (F.in_degree n).F.map f,
      comm' := λ i j hij, by { dsimp at hij, subst hij, simp }
    }
  }

lemma stupid (F : based_complex_functor) (n : ℕ)
  : F.to_complex_functor ⋙ homological_complex.eval (Module R) _ n = (F.in_degree n).F :=
@category_theory.functor.ext C _ (Module R) _
                            (F.to_complex_functor ⋙ homological_complex.eval (Module R) _ n)
                            (F.in_degree n).F
                            (λ X, rfl)
                            (λ X Y f, by { simp, refl })

noncomputable
def based_complex_functor.mk_nat_trans
  {F : based_complex_functor}
  {G : C ⥤ chain_complex (Module R) ℕ}
  (η : Π (i : ℕ), (F.in_degree i).F ⟶ (G ⋙ homological_complex.eval _ _ i))
  (η_comm_ds : ∀ i X, (η (i + 1)).app X ≫ (G.obj X).d (i + 1) i
                       = (F.differentials i).app X ≫ (η i).app X)
  : F.to_complex_functor ⟶ G := 
  let η' : Π (i : ℕ), (F.to_complex_functor ⋙ homological_complex.eval _ _ i)
                    ⟶ (G ⋙ homological_complex.eval _ _ i)
         := by intro i; rw stupid; exact η i
  in homological_complex.mk_nat_trans η' 
        (by { intros i j h X,
              dsimp at h, rw ← h,
              dsimp [based_complex_functor.to_complex_functor],
              rw chain_complex.of_d,
              refine eq.mp _ (η_comm_ds j X),
              symmetry,
              congr,
              { apply stupid },
              { apply eq_rec_heq },
              { apply stupid },
              { apply eq_rec_heq } })

lemma based_complex_functor.mk_nat_trans_apply 
  {F : based_complex_functor}
  {G : C ⥤ chain_complex (Module R) ℕ}
  (η : Π (i : ℕ), (F.in_degree i).F ⟶ (G ⋙ homological_complex.eval _ _ i))
  (η_comm_ds : ∀ i X, (η (i + 1)).app X ≫ (G.obj X).d (i + 1) i
                       = (F.differentials i).app X ≫ (η i).app X)
  (X : C) (n : ℕ)
  : ((based_complex_functor.mk_nat_trans η η_comm_ds).app X).f n = (η n).app X :=
begin
  dsimp [based_complex_functor.mk_nat_trans, homological_complex.mk_nat_trans],
  congr,
  apply stupid,
  apply cast_heq
end

-- dieck says it should be H_{n+1}(G_*(B_{n+1, j})) = 0 but it's actually H_{n+1}(G_*(B_{n, j})) = 0
def acyclic (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ)) := 
  ∀ n (i : (F.in_degree (n + 1)).indices), is_isomorphic ((G.obj ((F.in_degree (n+1)).models i)).homology n) 0

noncomputable
def lift_nat_trans_deg0 (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : (F.in_degree 0).F ⟶ (G ⋙ homological_complex.eval _ _ 0) :=
  (F.in_degree 0).map_out (G ⋙ homological_complex.eval _ _ 0)
                          (λ i, preim_of_homology_class (G.obj ((F.in_degree 0).models i))
                                                        0
                                                        (ϕ.app ((F.in_degree 0).models i)
                                                                (Module.to_homology ⟨(F.in_degree 0).basis i, by simp⟩)))

noncomputable
def lift_nat_trans_deg1 (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F.in_degree 1).F ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  have h : ∀ (i : (F.in_degree 1).indices), 
                   (G.obj ((F.in_degree 1).models i)).d_from 0
                     ((lift_nat_trans_deg0 F G H_acyclic ϕ).app ((F.in_degree 1).models i)
                         ((F.differentials 0).app
                           ((F.in_degree 1).models i)
                           ((F.in_degree 1).basis i)))
                         = 0,
  by { intro i,
       suffices : (lift_nat_trans_deg0 F G H_acyclic ϕ).app ((F.in_degree 1).models i)
                  ≫ (G.obj ((F.in_degree 1).models i)).d_from 0 = 0,
       exact congr_fun (congr_arg coe_fn this) ((F.differentials 0).app ((F.in_degree 1).models i) ((F.in_degree 1).basis i)),
       apply basis.ext ((F.in_degree 0).get_basis ((F.in_degree 1).models i)),
       intro j,
       simp },
  (F.in_degree 1).map_out (G ⋙ homological_complex.eval _ _ 1)
                          (λ i, preim_cycle_of_homology_zero _ _ _
                                (rfl : (complex_shape.down ℕ).rel 1 0)
                                (H_acyclic 0 i)
                                _
                                (h i))

noncomputable
def lift_nat_trans_degsucc (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (n : ℕ)
  (α : (F.in_degree n).F ⟶ (G ⋙ homological_complex.eval _ _ n))
  (β : (F.in_degree (n + 1)).F ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)))
  (H : ∀ X, β.app X ≫ (G.obj X).d (n + 1) n = (F.differentials n).app X ≫ α.app X)
  : (F.in_degree (n + 2)).F ⟶ (G ⋙ homological_complex.eval _ _ (n + 2)) := 
  (F.in_degree (n + 2)).map_out (G ⋙ homological_complex.eval _ _ (n + 2))
                                (λ i, 
  let F'' := F.in_degree (n + 2) in
  have h1 : (G.obj (F''.models i)).d_from (n + 1)
                    (β.app (F''.models i) ((F.differentials (n + 1)).app (F''.models i)
                        (F''.basis i)))
                        = 0,
  by { have h : (complex_shape.down ℕ).rel (n + 1) n := rfl, 
       rw homological_complex.d_from_eq _ h,
       change (homological_complex.X_next_iso (G.obj (F''.models i)) h).inv 
                 ((β.app (F''.models i) ≫ (G.obj (F''.models i)).d (n + 1) n)
                     ((F.differentials (n + 1)).app (F''.models i) (F''.basis i)))
             = 0,
       rw H,
       change (homological_complex.X_next_iso (G.obj (F''.models i)) h).inv 
               (α.app (F''.models i) ((F.differentials (n + 1) ≫ F.differentials n).app (F''.models i) (F''.basis i)))
             = 0,
       rw F.dd_eq_zero,
       simp },
  preim_cycle_of_homology_zero _ _ _
                               (rfl : (complex_shape.down ℕ).rel (n + 2) (n + 1))
                               (H_acyclic (n + 1) i)
                               _
                               h1)

lemma first_step_natural (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  (X : C)
  : (lift_nat_trans_deg1 F G H_acyclic ϕ).app X ≫ (G.obj X).d 1 0
  = (F.differentials 0).app X ≫ (lift_nat_trans_deg0 F G H_acyclic ϕ).app X :=
begin
  apply basis.ext (based_free_functor.get_basis (F.in_degree 1) X),
  intro p, cases p with i f, 
  dsimp [based_free_functor.get_basis, lift_nat_trans_deg1],
  rw [basis.mk_apply],
  simp,
  rw map_out_desc,
  simp,
  rw ← category_theory.comp_apply ((G.map f).f 1) ((G.obj X).d 1 0),
  rw (G.map f).comm',
  simp,
  rw preim_cycle_of_homology_zero_spec,
  rw ← category_theory.comp_apply _ ((G.map f).f 0),
  have h1 := (lift_nat_trans_deg0 F G H_acyclic ϕ).naturality' f,
  dsimp at h1,
  rw ← h1,
  dsimp,
  congr,
  rw ← category_theory.comp_apply,
  
  have h2 := (F.to_complex_functor.map f).comm' 1 0 _,
  delta based_complex_functor.to_complex_functor at h2,
  dsimp at h2,
  have : ∀ Y, (chain_complex.of (λ (n : ℕ), (F.in_degree n).F.obj Y)
                                (λ (n : ℕ), (F.differentials n).app Y)
                                (λ n, eq.trans (nat_trans.comp_app _ _ Y).symm
                                                (by rw F.dd_eq_zero n; refl))).d 1 0
              = (F.differentials 0).app Y,
  { intro Y, apply chain_complex.of_d },
  rw [← this X, ← this ((F.in_degree 1).models i)],
  rw h2.symm,
  refl,
  all_goals { apply complex_shape.down'_mk; refl }
end

lemma step_natural (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (n : ℕ)
  (α : (F.in_degree n).F ⟶ (G ⋙ homological_complex.eval _ _ n))
  (β : (F.in_degree (n + 1)).F ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)))
  (H : ∀ X, β.app X ≫ (G.obj X).d (n + 1) n = (F.differentials n).app X ≫ α.app X) (X : C)
  : (lift_nat_trans_degsucc F G H_acyclic n α β H).app X ≫ (G.obj X).d (n + 2) (n + 1)
  = (F.differentials (n + 1)).app X ≫ β.app X :=
begin
  apply basis.ext (based_free_functor.get_basis (F.in_degree (n + 2)) X),
  intro p, cases p with i f, 
  dsimp [based_free_functor.get_basis, lift_nat_trans_degsucc],
  rw [basis.mk_apply],
  simp,
  rw map_out_desc,
  simp,
  rw ← category_theory.comp_apply ((G.map f).f (n + 2)) ((G.obj X).d (n + 2) (n + 1)),
  rw (G.map f).comm',
  simp,
  rw preim_cycle_of_homology_zero_spec,
  rw ← category_theory.comp_apply _ ((G.map f).f (n + 1)),
  have h1 := β.naturality' f,
  dsimp at h1,
  rw ← h1,
  dsimp,
  congr,
  rw ← category_theory.comp_apply,
  
  have h2 := (F.to_complex_functor.map f).comm' (n + 2) (n + 1) _,
  delta based_complex_functor.to_complex_functor at h2,
  dsimp at h2,
  have : ∀ Y, (chain_complex.of (λ (n : ℕ), (F.in_degree n).F.obj Y)
                                (λ (n : ℕ), (F.differentials n).app Y)
                                (λ n, eq.trans (nat_trans.comp_app _ _ Y).symm
                                                (by rw F.dd_eq_zero n; refl))).d (n + 2) (n + 1)
              = (F.differentials (n + 1)).app Y,
  { intro Y, apply chain_complex.of_d },
  rw [← this X, ← this ((F.in_degree (n + 2)).models i)],
  rw h2.symm,
  refl,
  all_goals { apply complex_shape.down'_mk; refl }
end

structure lifted_nat_trans_pair (F : based_complex_functor)
                                (G : functor C (chain_complex (Module R) ℕ))
                                (n : ℕ) :=
(prev : (F.in_degree n).F       ⟶ (G ⋙ homological_complex.eval _ _ n))
(curr : (F.in_degree (n + 1)).F ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)))
(comm : ∀ X : C, nat_trans.app curr X ≫ (G.obj X).d (n + 1) n
               = (F.differentials n).app X ≫ nat_trans.app prev X)

noncomputable
def lift_nat_trans_nth_map (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : Π (n : ℕ), lifted_nat_trans_pair F G n
| 0       := ⟨lift_nat_trans_deg0 F G H_acyclic ϕ,
              lift_nat_trans_deg1 F G H_acyclic ϕ,
              first_step_natural F G H_acyclic ϕ⟩
| (n + 1) := match lift_nat_trans_nth_map n with
             | ⟨prev, curr, h⟩ := ⟨curr,
                                  lift_nat_trans_degsucc F G H_acyclic n prev curr h,
                                  step_natural F G H_acyclic n prev curr h⟩
             end

noncomputable
def lift_nat_trans (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : F.to_complex_functor ⟶ G :=
  based_complex_functor.mk_nat_trans (λ i, (lift_nat_trans_nth_map F G H_acyclic ϕ i).prev)
                                     (λ i, by { dsimp [lift_nat_trans_nth_map],
                                                generalize : lift_nat_trans_nth_map F G H_acyclic ϕ i = c,
                                                cases c,
                                                delta lift_nat_trans_nth_map._match_1,
                                                apply c_comm })

lemma lift_nat_trans_app0 (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  (X : C) (i : (F.in_degree 0).indices) (f : (F.in_degree 0).models i ⟶ X)
  (h : (G.obj X).d_from 0 (((lift_nat_trans F G H_acyclic ϕ).app X).f 0 ((F.in_degree 0).F.map f ((F.in_degree 0).basis i))) = 0)
  : Module.to_homology ⟨((lift_nat_trans F G H_acyclic ϕ).app X).f 0 ((F.in_degree 0).F.map f ((F.in_degree 0).basis i)), h⟩
  = (G ⋙ homology_functor (Module R) _ 0).map f
      (ϕ.app ((F.in_degree 0).models i) (Module.to_homology ⟨(F.in_degree 0).basis i, by simp⟩)) := 
begin
  delta lift_nat_trans,
  transitivity Module.to_homology ⟨(lift_nat_trans_deg0 F G H_acyclic ϕ).app X ((F.in_degree 0).F.map f ((F.in_degree 0).basis i)), by simp⟩,
  congr, apply based_complex_functor.mk_nat_trans_apply,
  dsimp [lift_nat_trans_deg0],
  rw map_out_desc,
  transitivity (G ⋙ homology_functor (Module R) _ 0).map f
                (Module.to_homology ⟨preim_of_homology_class (G.obj ((F.in_degree 0).models i)) 0 (ϕ.app ((F.in_degree 0).models i) (Module.to_homology ⟨(F.in_degree 0).basis i, by simp⟩)), by simp⟩),
  { simp only [homology.π_map_apply,
               category_theory.functor.comp_map,
               homology_functor_map,
               homological_complex.eval_map],
    delta Module.to_homology,
    congr,
    symmetry,
    transitivity (cycles_map (G.map f) 0) (Module.to_cycles _), refl,
    rw Module.cycles_map_to_cycles },
  { cases (preim_of_homology_class_spec (G.obj ((F.in_degree 0).models i)) 0
                                      (ϕ.app ((F.in_degree 0).models i)
                                        (Module.to_homology ⟨(F.in_degree 0).basis i, by simp⟩)))
        with h' H,
    congr,
    exact H }
end

lemma lift_nat_trans_spec (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
  (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
                               ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : whisker_right (lift_nat_trans F G H_acyclic ϕ) (homology_functor (Module R) _ 0) = ϕ := 
begin
  ext X : 2,
  apply homology.ext,
  have : kernel_subobject (homological_complex.d_from (F.to_complex_functor.obj X) 0) = ⊤, simp, 
  rw ← category_theory.subobject.is_iso_iff_mk_eq_top at this,
  let f : kernel (homological_complex.d_from (F.to_complex_functor.obj X) 0)
        ≅ (F.to_complex_functor.obj X).X 0 := @category_theory.as_iso _ _ _ _ _ this,
  let f' : ↑ (kernel_subobject (homological_complex.d_from (F.to_complex_functor.obj X) 0))
        ≅ (F.to_complex_functor.obj X).X 0,
  { transitivity,
    apply category_theory.subobject.underlying_iso,
    exact f },
  refine (category_theory.iso.cancel_iso_hom_left f'.symm _ _).mp _,
  apply basis.ext ((F.in_degree 0).get_basis X),
  intro p, cases p with i f,
  simp only [category_theory.whisker_right_app,
            category_theory.iso.trans_symm,
            category_theory.as_iso_inv,
            function.comp_app,
            category_theory.iso.symm_hom,
            category_theory.category.assoc,
            Module.coe_comp,
            category_theory.iso.trans_hom,
            based_free_functor.get_basis],
  rw [basis.mk_apply],
  transitivity (ϕ.app X) (Module.to_homology ⟨(F.in_degree 0).F.map f ((F.in_degree 0).basis i), (by simp)⟩),
  { transitivity (homology_functor (Module R) (complex_shape.down ℕ) 0).map ((lift_nat_trans F G H_acyclic ϕ).app X)
                  (Module.to_homology ⟨(F.in_degree 0).F.map f ((F.in_degree 0).basis i), (by simp)⟩),
    { congr, symmetry, 
      apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ this),
      simp },
    { dsimp [homology_functor],
      simp,
      rw (_ : (kernel_subobject_map (homological_complex.hom.sq_from ((lift_nat_trans F G H_acyclic ϕ).app X) 0))
            = cycles_map ((lift_nat_trans F G H_acyclic ϕ).app X) 0),
      rw Module.cycles_map_to_cycles,
      dsimp [subtype.val],
      transitivity Module.to_homology ⟨((lift_nat_trans F G H_acyclic ϕ).app X).f 0 ((F.in_degree 0).F.map f ((F.in_degree 0).basis i)), by simp⟩,
      refl,
      transitivity, apply lift_nat_trans_app0,
      rw [← category_theory.comp_apply (ϕ.app ((F.in_degree 0).models i)) _],
      rw ← ϕ.naturality,
      refine congr_arg (coe_fn (ϕ.app X)) _,
      simp, delta Module.to_homology,
      congr,
      apply Module.cycles_map_to_cycles, refl } },
  { apply congr_arg,
    delta Module.to_homology,
    delta Module.to_cycles,
    congr,
    simp,
    rw [← category_theory.comp_apply],
    transitivity ((subobject.underlying_iso (kernel.ι (homological_complex.d_from (F.to_complex_functor.obj X) 0)))
                  ≪≫ (@category_theory.as_iso _ _ _ _ _ this)).inv
                    (((F.in_degree 0).F.map f) ((F.in_degree 0).basis i)),
    { apply category_theory.eq_app_inv_of_app_hom_eq
              ((subobject.underlying_iso (kernel.ι (homological_complex.d_from (F.to_complex_functor.obj X) 0)))
                ≪≫ (@category_theory.as_iso _ _ _ _ _ this)),
      simp },
    refl }
end

-- def chain_htpy_of_lifts_deg0 (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
--   (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
--                                ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
--   (α β : F.to_complex_functor ⟶ G)
--   (Hα : whisker_right α (homology_functor (Module R) _ 0) = ϕ)
--   (Hβ : whisker_right β (homology_functor (Module R) _ 0) = ϕ)
--   : (F.in_degree 0).F ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
--   based_free_functor.map_out (F.in_degree 0) (G ⋙ homological_complex.eval _ _ 1)
--                              (λ i, by {  })

-- lemma lift_nat_trans_unique (F : based_complex_functor) (G : functor C (chain_complex (Module R) ℕ))
--   (H_acyclic : acyclic F G) (ϕ : (F.to_complex_functor ⋙ homology_functor (Module R) _ 0)
--                                ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
--   (α β : F.to_complex_functor ⟶ G)
--   (Hα : whisker_right α (homology_functor (Module R) _ 0) = ϕ)
--   (Hβ : whisker_right β (homology_functor (Module R) _ 0) = ϕ)
--   :


end