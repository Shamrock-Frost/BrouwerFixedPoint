import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import .linear_algebra .category_theory .homological_algebra

open category_theory category_theory.limits

local attribute [instance] category_theory.limits.has_zero_object.has_zero

section

universes u u' v v' idx

parameters {C : Type u} [category.{u'} C] {R : Type v} [comm_ring R]

structure functor_basis (F : C ⥤ (Module.{v'} R)) : Type (max u u' v (v' + 1) idx + 1) :=
(indices : Type idx)
(models : indices → C)
(basis_elem : Π (i : indices), F.obj (models i))
(lin_indep : ∀ (X : C), linear_independent R (λ p : (Σ (i : indices), models i ⟶ X),
                                                F.map p.snd (basis_elem p.fst)))
(spanning : ∀ (X : C), submodule.span R { x | ∃ (i : indices) (f : models i ⟶ X),
                                                F.map f (basis_elem i) = x } = ⊤)

noncomputable
def functor_basis.get_basis {F : C ⥤ Module.{v'} R} (b : functor_basis F) (X : C)
  : basis (Σ (i : b.indices), b.models i ⟶ X) R (F.obj X) :=
basis.mk (b.lin_indep X) $ le_of_eq $ by {
  rw ← b.spanning X, congr, ext, simp only [sigma.exists]
}

noncomputable
def functor_basis.map_out {F : C ⥤ Module.{v'} R} (b : functor_basis F)
  (G : functor C (Module.{v'} R)) (choices : Π (i : b.indices), G.obj (b.models i)) : F ⟶ G := {
    app := λ X, basis.constr (b.get_basis X) R (λ p, G.map p.snd (choices p.fst)),
    naturality' := by { 
      intros X Y f,
      apply basis.ext (b.get_basis X), rintro ⟨i, g⟩,
      rw [comp_apply, (_ : F.map f (b.get_basis X ⟨i, g⟩) = b.get_basis Y ⟨i, g ≫ f⟩)],
      simp only [basis.constr_basis, functor.map_comp, Module.coe_comp, 
                 function.comp_app],
      simp only [functor_basis.get_basis, basis.coe_mk, functor.map_comp,
                 Module.coe_comp]
     }
  }

lemma map_out_desc {F : C ⥤ Module.{v'} R} (b : functor_basis F)
  (G : C ⥤ Module.{v'} R) (choices : Π (i : b.indices), G.obj (b.models i))
  {X : C} (i : b.indices) (f : b.models i ⟶ X)
  : ((b.map_out G choices).app X (b.get_basis X ⟨i, f⟩)) = G.map f (choices i) :=
basis.constr_basis (b.get_basis X) R (λ p, G.map p.snd (choices p.fst)) ⟨i, f⟩

def complex_functor_basis (F : C ⥤ chain_complex (Module.{v'} R) ℕ) :=
  Π (n : ℕ), functor_basis (F ⋙ homological_complex.eval _ _ n)

lemma functor_basis.homology_ext
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ}
  (b : functor_basis (F ⋙ homological_complex.eval _ _ 0))
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (α β : F ⟶ G)
  (H : ∀ i, ∃ y : (G.obj (b.models i)).X 1, (α.app (b.models i)).f 0 (b.basis_elem i)
                                          = (β.app (b.models i)).f 0 (b.basis_elem i)
                                          + (G.obj (b.models i)).d 1 0 y)
  : whisker_right α (homology_functor _ _ 0) = whisker_right β (homology_functor _ _ 0) :=
begin
  ext X : 2, apply Module.homology_ext'',
  intros x hx, existsi 1,
  apply submodule.span_induction (submodule.eq_top_iff'.mp (b.spanning X) x),
  { rintros _ ⟨i, f, h⟩, subst h,
    obtain ⟨y, hy⟩ := H i,
    existsi (G.map f).f 1 y,
    rw [← comp_apply ((G.map f).f 1)],
    simp only [functor.comp_map, homological_complex.eval_map, Module.coe_comp,
               function.comp_app, homological_complex.hom.comm],
    rw [← comp_apply, ← homological_complex.comp_f, α.naturality],
    dsimp, rw hy, simp only [map_add],
    rw [← comp_apply, ← homological_complex.comp_f, ← β.naturality], refl },
  { existsi (0 : ((G.obj X).X 1)),
    rw [map_zero ((α.app X).f 0), map_zero ((β.app X).f 0), map_zero ((G.obj X).d 1 0)],
    simp only [add_zero] },
  { rintros u v ⟨y, h⟩ ⟨z, h'⟩,
    existsi (y + z : (G.obj X).X 1),
    rw [map_add ((α.app X).f 0), map_add ((β.app X).f 0), 
        map_add ((G.obj X).d 1 0), h, h'], 
    rw [add_assoc, add_assoc (((β.app X).f 0) u)], 
    exact congr_arg _ (add_left_comm _ _ _) },
  { rintros s u ⟨y, h⟩,
    existsi (s • y : (G.obj X).X 1),
    rw [map_smul ((α.app X).f 0), map_smul ((β.app X).f 0),
        map_smul ((G.obj X).d 1 0), h],
    apply smul_add }
end

-- dieck says it should be H_{n}(G_*(B_{n, j})) = 0 but we also need H_{n+1}(G_*(B_{n, j})) = 0

def acyclic
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ) := ∀ n, n > 0 →
    (∀ (i : (b n).indices), is_isomorphic ((G.obj ((b n).models i)).homology n) 0)
  ∧ (∀ (i : (b (n + 1)).indices), is_isomorphic ((G.obj ((b (n + 1)).models i)).homology n) 0)

noncomputable
def lift_nat_trans_deg0
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 0) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 0)
                (λ i, (G.obj ((b 0).models i)).preim_of_homology_class
                        (ϕ.app ((b 0).models i)
                               (Module.to_homology ⟨(b 0).basis_elem i, by
    simp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero,
               complex_shape.down_rel, nat.one_ne_zero,
  not_false_iff, linear_map.ker_zero]⟩)))

lemma lift_nat_trans_deg0_is_lift
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  (X : C)
  : ∀ x (h' : x ∈ linear_map.ker ((F.obj X).d_from 0))
        (h  : (lift_nat_trans_deg0 b G ϕ).app X x ∈ linear_map.ker ((G.obj X).d_from 0)),
    Module.to_homology ⟨(lift_nat_trans_deg0 b G ϕ).app X x, h⟩
    = ϕ.app X (Module.to_homology ⟨x, h'⟩) :=
    let lhs_hom : (F.obj X).X 0 ⟶ (G.obj X).homology 0 :=
          (lift_nat_trans_deg0 b G ϕ).app X
          ≫ inv (kernel_subobject (homological_complex.d_from (G.obj X) 0)).arrow
          ≫ homology.π _ _ _,
        rhs_hom : (F.obj X).X 0 ⟶ (G.obj X).homology 0 :=
          inv (kernel_subobject (homological_complex.d_from (F.obj X) 0)).arrow
          ≫ homology.π _ _ _
          ≫ ϕ.app X
    in suffices lhs_hom = rhs_hom,
    by { intros, have := congr_fun (congr_arg coe_fn this) x,
         refine eq.trans _ (eq.trans this (eq.symm _));
         dsimp only [lhs_hom, rhs_hom]; delta Module.to_homology; congr,
         { apply is_iso.eq_app_inv_of_app_hom_eq (kernel_subobject ((G.obj X).d_from 0)).arrow,
           apply Module.to_kernel_subobject_arrow },
         { apply is_iso.eq_app_inv_of_app_hom_eq (kernel_subobject ((F.obj X).d_from 0)).arrow,
           apply Module.to_kernel_subobject_arrow } },
    by { apply basis.ext ((b 0).get_basis X), rintro ⟨i, f⟩,
         simp only [lift_nat_trans_deg0, Module.coe_comp, function.comp_app],
         rw map_out_desc, 
         simp only [functor.comp_map, homological_complex.eval_map],
         obtain ⟨h, h'⟩ := (G.obj ((b 0).models i)).preim_of_homology_class_spec
                            (ϕ.app ((b 0).models i)
                            (Module.to_homology ⟨(b 0).basis_elem i, by
    simp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero,
               complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
               linear_map.ker_zero]⟩)),
         transitivity (G ⋙ homology_functor (Module R) _ 0).map f
                        (Module.to_homology
                          ⟨(G.obj ((b 0).models i)).preim_of_homology_class
                            (ϕ.app ((b 0).models i)
                                   (Module.to_homology ⟨(b 0).basis_elem i, by
    simp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero,
               complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
               linear_map.ker_zero]⟩)), h⟩),
         { rw [category_theory.functor.comp_map, homology_functor_map, homology.π_map_apply],
           apply congr_arg, symmetry,
           apply is_iso.eq_app_inv_of_app_hom_eq, simp only [kernel_subobject_map_arrow_apply, homological_complex.hom.sq_from_left, Module.to_kernel_subobject_arrow] },
         { rw [h', ← category_theory.comp_apply, ← ϕ.naturality],
           dsimp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero, 
                       complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
                       linear_map.ker_zero, homological_complex.d_to_comp_d_from],
           dsimp,
           rw homology.π_map_apply,
           congr,
           apply is_iso.eq_app_inv_of_app_hom_eq,
           simp only [functor_basis.get_basis, basis.mk_apply, 
                      kernel_subobject_map_arrow_apply, functor.comp_map,
                      homological_complex.hom.sq_from_left,
                      Module.to_kernel_subobject_arrow, homological_complex.eval_map] } }

lemma first_step_zero_in_homology
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  (i : (b 1).indices)
  (h : (lift_nat_trans_deg0 b G ϕ).app ((b 1).models i) 
         ((F.obj ((b 1).models i)).d 1 0 ((b 1).basis_elem i))
       ∈ linear_map.ker ((G.obj ((b 1).models i)).d_from 0))
  : Module.to_homology
      ⟨(lift_nat_trans_deg0 b G ϕ).app ((b 1).models i) 
        ((F.obj ((b 1).models i)).d 1 0 ((b 1).basis_elem i)), h⟩
    = (0 : ((G.obj ((b 1).models i)).homology 0)) :=
begin
  transitivity, apply lift_nat_trans_deg0_is_lift,
  simp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero, 
             complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
             linear_map.ker_zero],
  refine eq.trans _ (map_zero (ϕ.app ((b 1).models i))), congr,
  rw ← Module.to_homology_eq_zero (complex_shape.down_mk 1 0 (nat.zero_add 1)),
  apply linear_map.mem_range_self
end

noncomputable
def lift_nat_trans_step
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i, ψ.app ((b (n + 1)).models i)
                  ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
            ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  (zero_in_homology : ∀ i, Module.to_homology ⟨_, H i⟩ = (0 : (G.obj _).homology n))
  : (F ⋙ homological_complex.eval _ _ (n + 1)) ⟶ (G ⋙ homological_complex.eval _ _ (n + 1)) := 
  (b (n + 1)).map_out (G ⋙ homological_complex.eval _ _ (n + 1))
                      (λ i,  homological_complex.preim_cycle_of_to_homology_zero
                               _
                               (complex_shape.down_mk (n + 1) n rfl)
                               _
                               (H i)
                               (zero_in_homology i))

lemma step_chain_map
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (n : ℕ)
  (ψ : (F ⋙ homological_complex.eval _ _ n) ⟶ (G ⋙ homological_complex.eval _ _ n))
  (H : ∀ i, ψ.app ((b (n + 1)).models i)
                  ((F.obj ((b (n + 1)).models i)).d (n + 1) n ((b (n + 1)).basis_elem i))
            ∈ linear_map.ker ((G.obj ((b (n + 1)).models i)).d_from n))
  (zero_in_homology : ∀ i, Module.to_homology ⟨_, H i⟩ = (0 : (G.obj _).homology n))
  (X : C)
  : (lift_nat_trans_step b G n ψ H zero_in_homology).app X ≫ (G.obj X).d (n + 1) n
  = (F.obj X).d (n + 1) n ≫ ψ.app X :=
begin
  apply basis.ext ((b (n + 1)).get_basis X), rintro ⟨i, f⟩,
  dsimp [lift_nat_trans_step],
  rw map_out_desc,
  rw [category_theory.functor.comp_map, homological_complex.eval_map],
  rw ← category_theory.comp_apply ((G.map f).f (n + 1)) ((G.obj X).d (n + 1) n),
  rw (G.map f).comm' _ _ (complex_shape.down_mk (n + 1) n rfl),
  rw category_theory.comp_apply,
  rw homological_complex.preim_cycle_of_to_homology_zero_spec,
  rw ← category_theory.comp_apply _ ((G.map f).f n),
  rw [← homological_complex.eval_map, ← category_theory.functor.comp_map, ← ψ.naturality],
  apply congr_arg (ψ.app X), 
  dsimp,
  rw [← category_theory.comp_apply, ← (F.map f).comm' _ _ (complex_shape.down_mk (n + 1) n rfl)],
  dsimp [functor_basis.get_basis],
  rw basis.mk_apply
end

noncomputable
def lift_nat_trans_deg1
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 1) ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  lift_nat_trans_step b G 0 (lift_nat_trans_deg0 b G ϕ)
                      (by { intro,
    simp only [homological_complex.d_from_eq_zero, 
               complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
               linear_map.ker_zero, chain_complex.next_nat_zero] })
                      (λ i, first_step_zero_in_homology b G ϕ i _) 

noncomputable
def lift_nat_trans_nth_aux
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : Π (n : ℕ),
    Σ' (α : (F ⋙ homological_complex.eval _ _ n)     ⟶ (G ⋙ homological_complex.eval _ _ n))
       (β : (F ⋙ homological_complex.eval _ _ (n+1)) ⟶ (G ⋙ homological_complex.eval _ _ (n+1))),
    ∀ X : C, nat_trans.app β X ≫ (G.obj X).d (n + 1) n = (F.obj X).d (n + 1) n ≫ nat_trans.app α X
| 0       := have H : ∀ i, (lift_nat_trans_deg0 b G ϕ).app ((b 1).models i)
                             ((F.obj ((b 1).models i)).d 1 0 ((b 1).basis_elem i))
                           ∈ linear_map.ker ((G.obj ((b 1).models i)).d_from 0),
             by simp only [homological_complex.d_from_eq_zero, nat.one_ne_zero,
                           chain_complex.next_nat_zero, complex_shape.down_rel,
                           not_false_iff, linear_map.ker_zero, submodule.mem_top,
                           implies_true_iff],
             ⟨lift_nat_trans_deg0 b G ϕ, lift_nat_trans_deg1 b G ϕ,
              step_chain_map b G 0 (lift_nat_trans_deg0 b G ϕ) H
                             (λ i, first_step_zero_in_homology b G ϕ i (H i))⟩
| (n + 1) := match lift_nat_trans_nth_aux n with
             | ⟨prev, curr, h⟩ := 
             have H :
              ∀ i, curr.app ((b (n + 1 + 1)).models i)
                     ((F.obj ((b (n + 1 + 1)).models i)).d (n + 1 + 1) (n + 1)
                       ((b (n + 1 + 1)).basis_elem i))
                   ∈ linear_map.ker ((G.obj ((b (n + 1 + 1)).models i)).d_from (n + 1)),
             by { intro, simp only [linear_map.mem_ker],
                  rw ← category_theory.comp_apply,
                  rw homological_complex.d_from_eq _ (complex_shape.down_mk (n + 1) n rfl),
                  rw ← category_theory.category.assoc, rw h,
                  simp only [Module.coe_comp, function.comp_app], 
                  rw ← category_theory.comp_apply _ (homological_complex.d _ _ _),
                  simp only [homological_complex.d_comp_d, map_zero,
                             linear_map.zero_apply] },
             let H' := λ i, all_eq_zero_of_iso_zero ((H_acyclic (n + 1) n.zero_lt_succ).right i) in
             ⟨curr, lift_nat_trans_step b G (n + 1) curr H (λ i, H' i _), 
                    step_chain_map b G (n + 1) curr H (λ i, H' i _)⟩
             end

noncomputable
def lift_nat_trans
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : F ⟶ G :=
  homological_complex_functor.mk_nat_trans
    (λ n, (lift_nat_trans_nth_aux b G H_acyclic ϕ n).fst)
    (by { intros i j h X, dsimp at h, subst h, 
          dsimp only [lift_nat_trans_nth_aux],
          rcases lift_nat_trans_nth_aux b G H_acyclic ϕ j with ⟨prev, curr, h⟩, 
          apply h })

lemma lift_nat_trans_spec
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (ϕ : (F ⋙ homology_functor (Module R) _ 0) ⟶ (G ⋙ homology_functor (Module R) _ 0))
  : whisker_right (lift_nat_trans b G H_acyclic ϕ) (homology_functor (Module R) _ 0) = ϕ := 
begin
  apply nat_trans.ext, funext, apply Module.homology_ext', rintro ⟨x, h⟩,
  rw ← lift_nat_trans_deg0_is_lift b G ϕ X x h (by 
    simp only [homological_complex.d_from_eq_zero, chain_complex.next_nat_zero,
               complex_shape.down_rel, nat.one_ne_zero, not_false_iff,
               linear_map.ker_zero]),
  delta Module.to_homology, 
  simp only [whisker_right_app, homology_functor_map, homology.π_map_apply],
  refine congr_arg _ _,
  apply Module.cycles_map_to_cycles
end

noncomputable
def chain_htpy_of_lifts_deg0
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  : (F ⋙ homological_complex.eval _ _ 0) ⟶ (G ⋙ homological_complex.eval _ _ 1) :=
  (b 0).map_out (G ⋙ homological_complex.eval _ _ 1)
                (λ i, (G.obj ((b 0).models i)).preim_cycle_of_to_homology_zero
                        (complex_shape.down_mk 1 0 rfl)
                        (((α - β).app ((b 0).models i)).f 0 ((b 0).basis_elem i))
                        (by { refine eq.trans (congr_fun (congr_arg _ (homological_complex.d_from_eq_zero _ _)) _)
                                              (linear_map.zero_apply _),
                              simp only [chain_complex.next_nat_zero, not_false_iff,
                                         complex_shape.down_rel, nat.one_ne_zero] })
(begin
  have h1 := congr_fun (congr_arg nat_trans.app same_map_on_H0) ((b 0).models i),
  have h2 := whisker_eq (Module.as_hom_right (is_linear_map.mk' _ (Module.to_homology.homomorphism
                                                                    (F.obj ((b 0).models i)) 0)))
                        h1,
  let basis_elem' : linear_map.ker ((F.obj ((b 0).models i)).d_from 0)
                  := ⟨(b 0).basis_elem i,
    by simp only [homological_complex.d_from_eq_zero, not_false_iff,
                  complex_shape.down_rel, nat.one_ne_zero, 
                  linear_map.ker_zero, chain_complex.next_nat_zero]⟩, 
  have h3 := sub_eq_zero.mpr (congr_fun (congr_arg coe_fn h2) basis_elem'),
  refine eq.trans (eq.symm _) h3,
  repeat { rw [whisker_right_app, Module.to_homology_comp_homology_functor_map,
               comp_apply, Module.of_hom_apply] },
  rw ← map_sub, apply congr_arg, apply subtype.eq,
  simp only [linear_map.dom_restrict_apply, subtype.val_eq_coe,
             add_subgroup_class.coe_sub, linear_map.cod_restrict_apply,
             submodule.coe_mk, nat_trans.app_sub, linear_map.sub_apply,
             homological_complex.sub_f_apply]
end))

lemma chain_htpy_of_lifts_deg0_chain_htpy
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  (X : C)
  : (α.app X).f 0
  = ((chain_htpy_of_lifts_deg0 b G H_acyclic α β same_map_on_H0).app X ≫ (G.obj X).d 1 0)
  + (β.app X).f 0 :=
begin
  apply basis.ext ((b 0).get_basis X), rintro ⟨i, f⟩,
  dsimp [chain_htpy_of_lifts_deg0],
  rw [map_out_desc, category_theory.functor.comp_map, ← comp_apply,
      homological_complex.eval_map, (G.map f).comm, comp_apply,
      homological_complex.preim_cycle_of_to_homology_zero_spec],
  dsimp [functor_basis.get_basis],
  rw [basis.mk_apply, ← category_theory.comp_apply _ ((β.app _).f 0),
      ← homological_complex.comp_f, β.naturality,
      map_sub ((G.map f).f 0), sub_add,
      ← comp_apply, ← homological_complex.comp_f, α.naturality],
  simp only [homological_complex.comp_f, Module.coe_comp, sub_self, sub_zero]
end

noncomputable
def chain_htpy_of_lifts_step
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
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
                              (complex_shape.down_mk (n + 2) (n + 1) rfl) 
                              ((whisker_right α (homological_complex.eval (Module R) _ (n + 1))
                                - whisker_right β (homological_complex.eval (Module R) _ (n + 1))
                                - (homological_complex.d_nat_trans F (n + 1) n ≫ s)).app
                              ((b (n + 1)).models i) ((b (n + 1)).basis_elem i))
                              (by { rw homological_complex.d_from_eq _
                                        (complex_shape.down_mk (n + 1) n rfl),
                                    rw comp_apply,
                                    symmetry, apply iso.eq_app_inv_of_app_hom_eq,
                                    have := congr_fun (congr_arg coe_fn (H ((b (n + 1)).models i)))
                                                      ((b (n + 1)).basis_elem i),
                                    rw [comp_apply, comp_apply, ← sub_eq_zero] at this,
                                    rw ← map_sub ((G.obj ((b (n + 1)).models i)).d (n + 1) n)
                                       at this,
                                    refine eq.trans _ (eq.trans this.symm _),
                                    -- No idea why this works with the rewrite but not without it
                                    { rw ← linear_map.to_fun_eq_coe, 
                                      simp only [linear_map.to_fun_eq_coe, map_zero] },
                                    { rw [linear_map.add_apply, sub_add_eq_sub_sub_swap], refl } })
                              ((H_acyclic (n + 1) (nat.zero_lt_succ n)).left i))

lemma chain_htpy_of_lifts_step_chain_htpy
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
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
          + ((chain_htpy_of_lifts_step b G H_acyclic α β same_map_on_H0 n s h).app X
             ≫ (G.obj X).d (n + 2) (n + 1))
          + (nat_trans.app β X).f (n + 1) :=
begin
  intro,
  apply basis.ext ((b (n + 1)).get_basis X), rintro ⟨i, f⟩,
  dsimp [chain_htpy_of_lifts_step],
  rw map_out_desc,
  dsimp [],
  rw [← comp_apply ((G.map f).f (n + 2)), (G.map f).comm, comp_apply],
  rw homological_complex.preim_cycle_of_homology_zero_spec,
  simp only [homological_complex.d_nat_trans, functor_basis.get_basis,
             basis.mk_apply, functor.comp_map, homological_complex.eval_map],
  rw [map_sub ((G.map f).f (n + 1)), map_sub ((G.map f).f (n + 1))],
  have : ∀ a b c d e f : (G.obj X).X (n + 1),
        (a = c) → (b = e) → (f = d) → a = (b + (c - d - e)) + f,
  { intros a b c d e f h1 h2 h3, subst h1, subst h2, subst h3, 
    simp only [add_sub_cancel'_right, sub_add_cancel] },
  apply this;
  try { rw [← comp_apply, ← homological_complex.comp_f, nat_trans.naturality], refl },
  rw [← comp_apply ((F.map f).f (n + 1)), (F.map f).comm,
      comp_apply, ← comp_apply, ← homological_complex.eval_map,
      ← category_theory.functor.comp_map, nat_trans.naturality],
  refl
end


noncomputable
def lift_nat_trans_unique
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
  (H_acyclic : acyclic b G)
  (α β : F ⟶ G)
  (same_map_on_H0 : whisker_right α (homology_functor (Module R) _ 0)
                  = whisker_right β (homology_functor (Module R) _ 0))
  : natural_chain_homotopy α β := 
  chain_complex.mk_natural_chain_homotopy_rec
            (chain_htpy_of_lifts_deg0 b G H_acyclic α β same_map_on_H0) 
            (chain_htpy_of_lifts_deg0_chain_htpy b G H_acyclic α β same_map_on_H0)
            (chain_htpy_of_lifts_step b G H_acyclic α β same_map_on_H0)
            (chain_htpy_of_lifts_step_chain_htpy b G H_acyclic α β same_map_on_H0)

lemma lifts_of_nat_trans_H0_give_same_map_in_homology 
  {F : C ⥤ chain_complex (Module.{v'} R) ℕ} (b : complex_functor_basis F)
  (G : C ⥤ chain_complex (Module.{v'} R) ℕ)
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

