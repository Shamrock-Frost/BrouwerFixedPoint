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

import .homological_algebra

open category_theory algebraic_topology
open_locale big_operators

noncomputable
def free_complex_on_sset (R : Type*) [comm_ring R] : sSet ⥤ chain_complex (Module R) ℕ :=
  ((simplicial_object.whiskering _ _).obj (Module.free R)) ⋙ alternating_face_map_complex _

noncomputable
def singular_chain_complex (R : Type*) [comm_ring R] : Top ⥤ chain_complex (Module R) ℕ :=
  Top.to_sSet ⋙ free_complex_on_sset R

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

noncomputable
def singular_zero_simplex_of_pt {X : Top} (x0 : X)
  : (Top.to_sSet.obj X).obj (opposite.op (simplex_category.mk 0)) := 
  (continuous_map.const (topological_simplex 0) x0)

noncomputable
def simplex_to_chain {n : ℕ} {X : sSet}
  (σ : X.obj (opposite.op (simplex_category.mk n)))
  (R : Type*) [comm_ring R] : ((free_complex_on_sset R).obj X).X n :=
  finsupp.single σ 1

lemma singular_chain_complex_differential_desc (R : Type*) [comm_ring R] {X : Top} {n : ℕ}
  (σ : topological_simplex (n + 1) ⟶ X)
  : ((singular_chain_complex R).obj X).d (n + 1) n (finsupp.single σ 1)
  = ∑ (i : fin (n + 2)), (-1 : ℤ)^(i : ℕ)
  • simplex_to_chain (simplex_category.to_Top.map (simplex_category.δ i) ≫ σ) R := by {
    dsimp [singular_chain_complex, free_complex_on_sset],
    transitivity (alternating_face_map_complex.obj_d
                     (((simplicial_object.whiskering Type (Module R)).obj (Module.free R)).obj
                                                                         (Top.to_sSet.obj X)) n)
                     .to_fun
                     (finsupp.single σ 1),
    { congr, apply chain_complex.of_d },
    { simp [alternating_face_map_complex.obj_d],
      congr, ext i, congr,
      dsimp [simplex_to_chain],
      rw finsupp.eq_single_iff, split,
      { intros t h,
        rw finset.mem_singleton,
        simp at h,
        have : ((Module.free R).map ((Top.to_sSet.obj X).δ i) (finsupp.single σ 1)).to_fun t ≠ 0 := h,
        simp at this,
        exact and.left (finsupp.single_apply_ne_zero.mp this) },
      { change (((Module.free R).map ((Top.to_sSet.obj X).δ i) (finsupp.single σ 1)).to_fun
                  (simplex_category.to_Top.map (simplex_category.δ i) ≫ σ) = 1),
        simp,
        exact finsupp.single_eq_same } }
  }

lemma singular_chain_complex_differential_desc_deg_0 (R : Type*) [comm_ring R] {X : Top}
  (σ : topological_simplex 1 ⟶ X)
  : ((singular_chain_complex R).obj X).d 1 0 (finsupp.single σ 1)
  = simplex_to_chain (simplex_category.to_Top.map (@simplex_category.δ 0 0) ≫ σ) R 
  - simplex_to_chain (simplex_category.to_Top.map (@simplex_category.δ 0 1) ≫ σ) R :=
begin
  rw singular_chain_complex_differential_desc,
  rw finset.sum_eq_add_of_mem (0 : fin 2) 1 (finset.mem_univ _) (finset.mem_univ _),
  { simp, rw sub_eq_add_neg },
  { simp },
  { intros c H' H, exfalso, cases c with c hc, cases H,
    cases c, contradiction, cases c, contradiction,
    rw [nat.succ_lt_succ_iff, nat.succ_lt_succ_iff] at hc,
    exact not_lt_zero' hc }
end

