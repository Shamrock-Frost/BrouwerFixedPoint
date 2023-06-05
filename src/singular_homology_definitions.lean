import .simplices
import algebraic_topology.alternating_face_map_complex
import algebraic_topology.simplicial_set
import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex
import category_theory.adjunction.limits
import algebra.category.Module.colimits

import .homological_algebra
import .preserves_colimits_functor_category .alternating_face_map_complex .Module_AB4

open category_theory algebraic_topology
open_locale big_operators

noncomputable
def free_complex_on_sset (R : Type*) [comm_ring R] : sSet ⥤ chain_complex (Module R) ℕ :=
  ((simplicial_object.whiskering _ _).obj (Module.free R)) ⋙ alternating_face_map_complex _

noncomputable
def singular_chain_complex (R : Type*) [comm_ring R] : Top ⥤ chain_complex (Module R) ℕ :=
  Top.to_sSet' ⋙ free_complex_on_sset R

noncomputable
def singular_chain_complex_of_pair (R : Type*) [comm_ring R]
  : arrow Top ⥤ chain_complex (Module R) ℕ := 
  category_theory.functor.map_arrow (singular_chain_complex R)
  ⋙ coker_functor (chain_complex (Module R) ℕ)

noncomputable
def singular_homology (R : Type*) [comm_ring R] (n : ℕ) : Top ⥤ Module R :=
  singular_chain_complex R ⋙ homology_functor _ _ n

noncomputable
def singular_homology_of_pair (R : Type*) [comm_ring R] (n : ℕ) : arrow Top ⥤ Module R :=
  singular_chain_complex_of_pair R ⋙ homology_functor _ _ n

def singular_zero_simplex_of_pt {X : Top} (x0 : X)
  : (Top.to_sSet'.obj X).obj (opposite.op (simplex_category.mk 0)) := 
  (continuous_map.const (topological_simplex 0) x0)

noncomputable
def simplex_to_chain {n : ℕ} {X : sSet}
  (σ : X.obj (opposite.op (simplex_category.mk n)))
  (R : Type*) [comm_ring R] : ((free_complex_on_sset R).obj X).X n :=
  finsupp.single σ 1

-- Should mark this as simp and use it more widely maybe?
lemma singular_chain_complex_map
  (R : Type*) [comm_ring R] (n : ℕ) {X Y : Top} 
  (f : X ⟶ Y) (σ : (Top.to_sSet'.obj X).obj (opposite.op (simplex_category.mk n)))
  : ((singular_chain_complex R).map f).f n (finsupp.single σ 1) 
  = finsupp.single (σ ≫ f) 1 := finsupp.map_domain_single

lemma singular_chain_complex_differential_desc (R : Type*) [comm_ring R] {X : Top} {n : ℕ}
  (σ : Top.of (topological_simplex (n + 1)) ⟶ X)
  : ((singular_chain_complex R).obj X).d (n + 1) n (finsupp.single σ 1)
  = ∑ (i : fin (n + 2)), (-1 : ℤ)^(i : ℕ)
  • simplex_to_chain (simplex_category.to_Top'.map (simplex_category.δ i) ≫ σ) R := by {
    dsimp only [singular_chain_complex, free_complex_on_sset],
    transitivity (alternating_face_map_complex.obj_d
                     (((simplicial_object.whiskering Type (Module R)).obj (Module.free R)).obj
                                                                          (Top.to_sSet'.obj X)) n)
                     .to_fun
                     (finsupp.single σ 1),
    { congr, apply chain_complex.of_d },
    { simp only [alternating_face_map_complex.obj_d, linear_map.to_fun_eq_coe,
                 linear_map.coe_fn_sum, fintype.sum_apply, linear_map.smul_apply],
      congr, ext i, congr,
      dsimp only [simplex_to_chain],
      rw finsupp.eq_single_iff, split,
      { intros t h,
        rw finset.mem_singleton,
        simp only [finsupp.mem_support_iff, ne.def] at h,
        change ((Module.free R).map ((Top.to_sSet'.obj X).δ i) (finsupp.single σ 1)).to_fun t ≠ 0 at h,
        simp only [Module.free_map, finsupp.lmap_domain_apply, finsupp.map_domain_single, ne.def] at h,
        exact and.left (finsupp.single_apply_ne_zero.mp h) },
      { change (((Module.free R).map ((Top.to_sSet'.obj X).δ i) (finsupp.single σ 1)).to_fun
                  (simplex_category.to_Top'.map (simplex_category.δ i) ≫ σ) = 1),
        simp only [Module.free_map, finsupp.lmap_domain_apply, finsupp.map_domain_single],
        convert finsupp.single_eq_same } }
  }

lemma singular_chain_complex_differential_desc_deg_0 (R : Type*) [comm_ring R] {X : Top}
  (σ : Top.of (topological_simplex 1) ⟶ X)
  : ((singular_chain_complex R).obj X).d 1 0 (finsupp.single σ 1)
  = simplex_to_chain (simplex_category.to_Top'.map (@simplex_category.δ 0 0) ≫ σ) R 
  - simplex_to_chain (simplex_category.to_Top'.map (@simplex_category.δ 0 1) ≫ σ) R :=
begin
  rw singular_chain_complex_differential_desc,
  rw finset.sum_eq_add_of_mem (0 : fin 2) 1 (finset.mem_univ _) (finset.mem_univ _),
  { simp only [fin.coe_zero, pow_zero, one_zsmul, fin.coe_one, pow_one, neg_smul],
    rw sub_eq_add_neg },
  { simp only [ne.def, fin.zero_eq_one_iff, nat.succ_succ_ne_one, not_false_iff]},
  { intros c H' H, exfalso, cases c with c hc, cases H,
    cases c, contradiction, cases c, contradiction,
    rw [nat.succ_lt_succ_iff, nat.succ_lt_succ_iff] at hc,
    exact not_lt_zero' hc }
end

lemma singular_chain_complex_map_inj (R : Type*) [comm_ring R] {X Y : Top} 
  (f : X ⟶ Y) (hf : function.injective f) (n : ℕ) 
  : function.injective (((singular_chain_complex R).map f).f n) :=
begin
  refine finsupp.map_domain_injective (λ σ τ hστ, _),
  ext p,
  have := congr_arg (λ g : topological_simplex n → Y, g p)
                    (congr_arg continuous_map.to_fun hστ),
  exact hf this
end

noncomputable
instance singular_chain_complex_preserves_coprod (R : Type*) [comm_ring R] {J : Type} (f : J → Top)
  : limits.preserves_colimit (discrete.functor f) (singular_chain_complex R) :=
begin
  apply_with limits.comp_preserves_colimit {instances:=ff},
  { apply Top.to_sSet'_preserves_coprod },
  { apply_with limits.comp_preserves_colimit {instances:=ff},
    { apply_with limits.preserves_colimits_of_shape.preserves_colimit {instances:=ff},
      apply_with category_theory.whiskering_right_preserves_colimits_of_shape {instances:=ff},
      apply_instance,
      apply (Module.adj R).left_adjoint_preserves_colimits.preserves_colimits_of_shape },
    { apply category_theory.limits.preserves_colimits_of_size.preserves_colimits_of_shape.preserves_colimit,
      apply alternating_face_map_complex.preserves_colimits } }
end

noncomputable
instance singular_homology_preserves_coprod (R : Type*) [comm_ring R] (n : ℕ) {J : Type} (f : J → Top)
  : limits.preserves_colimit (discrete.functor f) (singular_homology R n) :=
begin
  apply_with limits.comp_preserves_colimit {instances:=ff},
  { apply_instance },
  { let := @category_theory.homology_functor_preserves_coproducts (Module R) (Module.Module_category R) ℕ
             (complex_shape.down ℕ) J _,
    letI := (λ (J : Type), limits.has_colimits_of_shape_of_has_colimits_of_size : limits.has_coproducts (Module R)),
    apply_instance}
end

