import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import .linear_algebra .category_theory .homological_algebra

open category_theory category_theory.limits

local attribute [instance] category_theory.limits.has_zero_object.has_zero

section

universes u uhom v vhom w

parameters {C : Type u} [category.{uhom} C] {R : Type v} [comm_ring R]

structure functor_basis (F : C ⥤ (Module.{vhom} R)) : Type (max u uhom v (vhom + 1) w + 1) :=
(indices : Type w)
(models : indices → C)
(basis_elem : Π (i : indices), F.obj (models i))
(lin_indep : ∀ (X : C), linear_independent R (λ p : (Σ (i : indices), models i ⟶ X),
                                                F.map p.snd (basis_elem p.fst)))
(spanning : ∀ (X : C), submodule.span R { x | ∃ (i : indices) (f : models i ⟶ X), F.map f (basis_elem i) = x } = ⊤)

noncomputable
def functor_basis.get_basis {F : C ⥤ Module.{vhom} R} (b : functor_basis F) (X : C)
  : basis (Σ (i : b.indices), b.models i ⟶ X) R (F.obj X) :=
basis.mk (b.lin_indep X) (by { rw ← b.spanning X, congr, ext, simp })

noncomputable
def functor_basis.map_out {F : C ⥤ Module.{vhom} R} (b : functor_basis F) (G : functor C (Module.{vhom} R))
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

lemma map_out_desc {F : C ⥤ Module.{vhom} R} (b : functor_basis F) (G : C ⥤ Module.{vhom} R)
  (choices : Π (i : b.indices), G.obj (b.models i))
  {X : C} (i : b.indices) (f : b.models i ⟶ X)
  : ((b.map_out G choices).app X (b.get_basis X ⟨i, f⟩))
  = G.map f (choices i) :=
basis.constr_basis (b.get_basis X) R (λ p, G.map p.2 (choices p.1)) ⟨i, f⟩

def complex_functor_basis (F : C ⥤ chain_complex (Module.{vhom} R) ℕ) :=
  Π (n : ℕ), functor_basis (F ⋙ homological_complex.eval _ _ n)

lemma functor_basis.homology_map_ext 
  {F : C ⥤ chain_complex (Module.{vhom} R) ℕ}
  (b : functor_basis (F ⋙ homological_complex.eval _ _ 0))
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (α β : F ⟶ G)
  (H : ∀ i : b.indices, ∃ y : (G.obj (b.models i)).X 1,
        (α.app (b.models i)).f 0 (b.basis_elem i)
        = (β.app (b.models i)).f 0 (b.basis_elem i)
        + (G.obj (b.models i)).d 1 0 y)
  : whisker_right α (homology_functor _ _ 0) = whisker_right β (homology_functor _ _ 0) :=
begin
  ext X : 2,
  apply homology.ext,
  have h1 : is_iso (category_theory.limits.kernel.ι ((F.obj X).d_from 0)),
  { rw (F.obj X).d_from_eq_zero,
    apply category_theory.limits.kernel.ι_zero_is_iso,
    simp },
  let i1 := @category_theory.as_iso _ _ _ _ _ h1,
  let i2 : Module.of R (linear_map.ker ((F.obj X).d_from 0)) ≅ (F.obj X).X 0 := {
    hom := (linear_map.ker ((F.obj X).d_from 0)).subtype,
    inv := linear_map.cod_restrict (linear_map.ker ((F.obj X).d_from 0)) linear_map.id
                                   (by intros; simp),
    hom_inv_id' := by { ext, refl },
    inv_hom_id' := by { ext, refl }
  },
  let : ↑(kernel_subobject ((F.obj X).d_from 0)) ≅ (F.obj X).X 0 :=
    category_theory.limits.kernel_subobject_iso ((F.obj X).d_from 0) ≪≫ i1,
  apply (category_theory.iso.cancel_iso_inv_left this _ _).mp,
  apply basis.ext (b.get_basis X),
  intro p, cases p with i f,
  delta functor_basis.get_basis, rw basis.mk_apply,
  rw [category_theory.functor.comp_map, homological_complex.eval_map],
  rw [← category_theory.category.assoc, ← category_theory.category.assoc],
  rw (_ : this.inv ≫ homology.π ((F.obj X).d_to 0) ((F.obj X).d_from 0) _
        = i2.inv ≫ Module.of_hom (is_linear_map.mk' _ (Module.to_homology.homomorphism (F.obj X) 0))),
  swap,
  { ext : 1, simp, delta Module.to_homology, simp,
    congr,
    symmetry, 
    apply category_theory.eq_app_inv_of_app_hom_eq i1,
    simp },
  cases H i with y hy,
  rw [category_theory.category.assoc, category_theory.category.assoc,
      category_theory.whisker_right_app, category_theory.whisker_right_app],
  transitivity, exact congr_fun (congr_arg coe_fn (congr_arg2 category_theory.category_struct.comp rfl (Module.to_homology_comp_homology_functor_map (α.app X) 0))) ((F.map f).f 0 (b.basis_elem i)),
  symmetry, transitivity, 
  exact congr_fun (congr_arg coe_fn (congr_arg2 category_theory.category_struct.comp rfl (Module.to_homology_comp_homology_functor_map (β.app X) 0))) ((F.map f).f 0 (b.basis_elem i)),
  simp,
  symmetry,
  rw [submodule_restrict_app, submodule_restrict_app],
  simp,
  refine Module.to_homology_ext ((G.map f).f 1 y) _,
  rw ← category_theory.comp_apply ((G.map f).f 1),
  rw (G.map f).comm',
  simp only [function.comp_app, Module.coe_comp, linear_map.cod_restrict_apply, subtype.val_eq_coe],
  rw [← category_theory.comp_apply, ← category_theory.comp_apply,
      ← homological_complex.comp_f, ← homological_complex.comp_f],
  simp,
  rw ← map_add ((G.map f).f 0),
  exact congr_arg _ hy,
  dsimp, refl
end

-- dieck says it should be H_{n+1}(G_*(B_{n+1, j})) = 0 but it's actually
-- H_{n+1}(G_*(B_{n, j})) = 0 and H_n(G_*(B_{n, j})) = 0
def acyclic {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
            (G : C ⥤ chain_complex (Module.{vhom} R) ℕ) := 
  ∀ n k, n > 0 → (k = n ∨ k = n + 1)
       → ∀ (i : (b k).indices), is_isomorphic ((G.obj ((b k).models i)).homology n) 0

noncomputable
def lift_nat_trans_deg0 {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 0) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 0)
                (λ i, (G.obj ((b 0).models i)).preim_of_homology_class
                        (ϕ.app ((b 0).models i)
                                (Module.to_homology ⟨(b 0).basis_elem i,
                                                    by simp⟩)))

lemma lift_nat_trans_deg0_is_lift {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  (X : C)
  : ∀ x (h' : x ∈ linear_map.ker ((F.obj X).d_from 0))
        (h  : (lift_nat_trans_deg0 b G ϕ).app X x ∈ linear_map.ker ((G.obj X).d_from 0)),
    Module.to_homology ⟨(lift_nat_trans_deg0 b G ϕ).app X x, h⟩
    = ϕ.app X (Module.to_homology ⟨x, h'⟩) :=
  let lhs_hom : (F.obj X).X 0 ⟶ (G.obj X).homology 0 :=
    (lift_nat_trans_deg0 b G ϕ).app X
    ≫ (@category_theory.as_iso _ _ _ _ _
                               ((category_theory.subobject.is_iso_iff_mk_eq_top 
                                  (kernel_subobject (homological_complex.d_from (G.obj X) 0)).arrow).mpr 
                                    (by simp))).inv
    ≫ homology.π _ _ _,
      rhs_hom : (F.obj X).X 0 ⟶ (G.obj X).homology 0 :=
    (@category_theory.as_iso _ _ _ _ _
                             ((category_theory.subobject.is_iso_iff_mk_eq_top 
                               (kernel_subobject (homological_complex.d_from (F.obj X) 0)).arrow).mpr 
                                 (by simp))).inv
    ≫ homology.π _ _ _
    ≫ ϕ.app X
  in suffices lhs_hom = rhs_hom,
     by { intros,
          have := congr_fun (congr_arg coe_fn this) x,
          refine eq.trans _ (eq.trans this _),
          { dsimp [lhs_hom],
            -- This shows up in several places in the file, should def be a lemma
            delta Module.to_homology,
            congr,
            delta Module.to_cycles, delta Module.to_kernel_subobject,
            simp,
            apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ _),
            simp },
          { dsimp [rhs_hom],
            delta Module.to_homology,
            congr,
            delta Module.to_cycles, delta Module.to_kernel_subobject,
            simp,
            symmetry,
            apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ _),
            simp } },
     by { apply basis.ext ((b 0).get_basis X),
          intro p, cases p with i f,
          simp [lift_nat_trans_deg0],
          rw map_out_desc,
          dsimp,
          cases homological_complex.preim_of_homology_class_spec
                  (G.obj ((b 0).models i))
                  (ϕ.app ((b 0).models i)
                  (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩)),
          transitivity (G ⋙ homology_functor (Module R) _ 0).map f
                        (Module.to_homology
                          ⟨(G.obj ((b 0).models i)).preim_of_homology_class
                            (ϕ.app ((b 0).models i)
                                   (Module.to_homology ⟨(b 0).basis_elem i, by simp⟩)),
                           w⟩),
          { dsimp, delta Module.to_homology,
            rw homology.π_map_apply,
            congr,
            delta Module.to_cycles, delta Module.to_kernel_subobject,
            simp,
            symmetry,
            apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ _),
            simp },
          { rw h,
            rw [← category_theory.comp_apply, ← ϕ.naturality],
            delta Module.to_homology, 
            dsimp,
            rw homology.π_map_apply,
            congr,
            apply category_theory.eq_app_inv_of_app_hom_eq (@category_theory.as_iso _ _ _ _ _ _),
            simp,
            symmetry,
            apply basis.mk_apply } }

noncomputable
def lift_nat_trans_step {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : functor C (chain_complex (Module.{vhom} R) ℕ))
  (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i : (b (n + 1)).indices, ψ.app ((b (n + 1)).models i) ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
                                ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  (zero_in_homology : ∀ i, Module.to_homology ⟨_, H i⟩ = (0 : (G.obj ((b (n + 1)).models i)).homology n))
  : (F ⋙ homological_complex.eval _ _ (n + 1)) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)) := 
  (b (n + 1)).map_out (G ⋙ homological_complex.eval _ _ (n + 1))
                      (λ i, 
  let F'  := F ⋙ homological_complex.eval _ _ (n + 1),
      m   := (b (n + 1)).models i,
      b_m := (b (n + 1)).basis_elem i in
  homological_complex.preim_cycle_of_to_homology_zero
    _
    (rfl : (complex_shape.down ℕ).rel (n + 1) n)
    _
    (H i)
    (zero_in_homology i))

lemma step_chain_map {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i : (b (n + 1)).indices, ψ.app ((b (n + 1)).models i) ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
                                ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  (zero_in_homology : ∀ i, Module.to_homology ⟨_, H i⟩ = (0 : (G.obj ((b (n + 1)).models i)).homology n))
  (X : C)
  : (lift_nat_trans_step b G n ψ H zero_in_homology).app X ≫ (G.obj X).d (n + 1) n
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
  rw homological_complex.preim_cycle_of_to_homology_zero_spec,
  rw ← category_theory.comp_apply _ ((G.map f).f n),
  have := ψ.naturality' f,
  dsimp at this, rw ← this,
  rw category_theory.comp_apply,
  congr,
  rw [← category_theory.comp_apply, ← (F.map f).comm' _ _ (complex_shape.down_mk (n + 1) n rfl)],
  dsimp [functor_basis.get_basis],
  rw basis.mk_apply
end

lemma first_step_zero_in_homology {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  (i : (b (0 + 1)).indices)
  (h : (lift_nat_trans_deg0 b G ϕ).app ((b (0 + 1)).models i) 
        ((F.obj ((b (0 + 1)).models i)).d (0 + 1) 0 ((b (0 + 1)).basis_elem i))
        ∈ linear_map.ker ((G.obj ((b (0 + 1)).models i)).d_from 0))
  : Module.to_homology
      ⟨(lift_nat_trans_deg0 b G ϕ).app ((b (0 + 1)).models i) 
        ((F.obj ((b (0 + 1)).models i)).d (0 + 1) 0 ((b (0 + 1)).basis_elem i)), h⟩
    = (0 : ((G.obj ((b (0 + 1)).models i)).homology 0)) :=
begin
  transitivity, apply lift_nat_trans_deg0_is_lift, simp,
  transitivity ϕ.app ((b (0 + 1)).models i) 0,
  congr,
  delta Module.to_homology,
  delta homology.π,
  rw ← Module.range_mkq_cokernel_iso_range_quotient_inv,
  dsimp,
  refine eq.trans (congr_arg _ _) (map_zero _),
  refine (submodule.quotient.mk_eq_zero _).mpr _,
  simp,
  let y : image_subobject (homological_complex.d_to (F.obj ((b (0 + 1)).models i)) 0),
  { refine (image_subobject_iso _ ≪≫ Module.image_iso_range _).inv _,
    refine subtype.mk (((F.obj ((b (0 + 1)).models i)).d (0 + 1) 0)
                          ((b (0 + 1)).basis_elem i))
                      _,
    have h : 0 + 1 = 1 := rfl,
    rw homological_complex.d_to_eq _ (complex_shape.down_mk 1 0 h),
    existsi (homological_complex.X_prev_iso (F.obj ((b (0 + 1)).models i)) _).inv ((b (0 + 1)).basis_elem i),
    rw ← category_theory.comp_apply,
    rw ← category_theory.category.assoc,
    rw iso.inv_hom_id,
    simp },
  existsi y,
  delta Module.to_cycles,
  delta Module.to_kernel_subobject,
  dsimp,
  apply category_theory.eq_app_inv_of_app_hom_eq,
  apply category_theory.eq_app_inv_of_app_hom_eq,
  apply submodule.injective_subtype,
  transitivity (F.obj ((b (0 + 1)).models i)).d (0 + 1) 0 ((b (0 + 1)).basis_elem i),
  rw Module.kernel_iso_ker_hom_ker_subtype_apply,
  simp [y],
  rw ← category_theory.comp_apply,
  rw category_theory.limits.image_subobject_arrow',
  simp,
  refl,
  simp
end
        

noncomputable
def lift_nat_trans_deg1 {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 1) ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  lift_nat_trans_step b G 0 (lift_nat_trans_deg0 b G ϕ)
                      (by { intro, simp })
                      (λ i, first_step_zero_in_homology b G ϕ i _) 

noncomputable
def lift_nat_trans_nth_map {F : C ⥤ chain_complex (Module R) ℕ} (b : complex_functor_basis F)
                           (G : C ⥤ chain_complex (Module R) ℕ)
                           (H_acyclic : acyclic b G)
                           (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                              ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : Π (n : ℕ),
    Σ' (α : (F ⋙ homological_complex.eval _ _ n)       ⟶ (G ⋙ homological_complex.eval _ _ n))
       (β : (F ⋙ homological_complex.eval _ _ (n + 1)) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1))),
    ∀ X : C, nat_trans.app β X ≫ (G.obj X).d (n + 1) n = (F.obj X).d (n + 1) n ≫ nat_trans.app α X
| 0       := have H :
              ∀ (i : (b (0 + 1)).indices),
                (lift_nat_trans_deg0 b G ϕ).app ((b (0 + 1)).models i)
                    ((F.obj ((b (0 + 1)).models i)).d (0 + 1) 0 ((b (0 + 1)).basis_elem i)) ∈
                  linear_map.ker (homological_complex.d_from (G.obj ((b (0 + 1)).models i)) 0),
             by simp,
             ⟨lift_nat_trans_deg0 b G ϕ, lift_nat_trans_deg1 b G ϕ,
              step_chain_map b G 0 (lift_nat_trans_deg0 b G ϕ) H
                             (λ i, first_step_zero_in_homology b G ϕ i (H i))⟩
| (n + 1) := match lift_nat_trans_nth_map n with
             | ⟨prev, curr, h⟩ := 
             have H :
              ∀ (i : (b (n + 1 + 1)).indices),
                curr.app ((b (n + 1 + 1)).models i)
                    ((F.obj ((b (n + 1 + 1)).models i)).d (n + 1 + 1) (n + 1) ((b (n + 1 + 1)).basis_elem i)) ∈
                  linear_map.ker (homological_complex.d_from (G.obj ((b (n + 1 + 1)).models i)) (n + 1)),
             by { intro, simp, rw ← category_theory.comp_apply,
                  rw homological_complex.d_from_eq _ (complex_shape.down_mk (n + 1) n rfl),
                  rw ← category_theory.category.assoc, rw h, simp, 
                  rw ← category_theory.comp_apply _ (homological_complex.d _ _ _),
                  simp },
             ⟨curr,
              lift_nat_trans_step b G (n + 1) curr H
                (by { intro, apply all_eq_zero_of_iso_zero, 
                      apply H_acyclic, 
                      apply nat.zero_lt_succ,
                      right, refl }),
              step_chain_map b G (n + 1) curr H
                (by { intro, apply all_eq_zero_of_iso_zero, 
                      apply H_acyclic, 
                      apply nat.zero_lt_succ,
                      right, refl })⟩
             end

noncomputable
def lift_nat_trans {F : C ⥤ chain_complex (Module R) ℕ} (b : complex_functor_basis F)
                   (G : C ⥤ chain_complex (Module R) ℕ)
                   (H_acyclic : acyclic b G)
                   (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                      ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : F ⟶ G :=
  homological_complex_functor.mk_nat_trans
    (λ n, (lift_nat_trans_nth_map b G H_acyclic ϕ n).fst)
    (by { intros i j h X,
          dsimp at h, subst h,
          dsimp [lift_nat_trans_nth_map],
          generalize : lift_nat_trans_nth_map b G H_acyclic ϕ j = p,
          rcases p with ⟨prev, curr, h⟩,
          delta lift_nat_trans_nth_map._match_1, simp,
          apply h })

lemma lift_nat_trans_spec {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
                          (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
                          (H_acyclic : acyclic b G)
                          (ϕ : (F ⋙ homology_functor (Module R) _ 0)
                             ⟶ (G ⋙ homology_functor (Module R) _ 0)) 
  : whisker_right (lift_nat_trans b G H_acyclic ϕ) (homology_functor (Module R) _ 0) = ϕ := 
begin
  ext X x,
  cases x with x h,
  rw ← lift_nat_trans_deg0_is_lift b G ϕ X x h (by simp),
  delta Module.to_homology, simp,
  refine congr_arg _ _,
  apply Module.cycles_map_to_cycles
end

noncomputable
def chain_htpy_of_lifts_deg0 {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
                             (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
                             (H_acyclic : acyclic b G)
                             (α β : F ⟶ G)
                             (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                                             = whisker_right β (homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 1)
                (λ i, (G.obj ((b 0).models i)).preim_cycle_of_to_homology_zero
                        (rfl : (complex_shape.down ℕ).rel 1 0)
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
  {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
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
  rw homological_complex.preim_cycle_of_to_homology_zero_spec,
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
def chain_htpy_of_lifts_step {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
                             (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
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
                      (λ i, (G.obj ((b (n + 1)).models i)).preim_cycle_of_homology_zero
                              (rfl : (complex_shape.down ℕ).rel (n + 2) (n + 1)) 
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
                                    simp })
                              (by { apply H_acyclic, apply nat.zero_lt_succ, left, refl }))

lemma chain_htpy_of_lifts_step_chain_htpy
  {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
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
  rw homological_complex.preim_cycle_of_homology_zero_spec,
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
def lift_nat_trans_unique {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
                          (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
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

lemma lifts_of_nat_trans_H0_give_same_map_in_homology 
  {F : C ⥤ chain_complex (Module.{vhom} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{vhom} R) ℕ)
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

