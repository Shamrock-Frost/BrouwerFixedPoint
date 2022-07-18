import analysis.convex.basic analysis.convex.combination
import .homotopy_invariance 

section

parameters {ι : Type} [fintype ι]
parameters {D : set (ι → ℝ)} (hConvex : convex ℝ D)

def convex_combination {ι' : Type} [fintype ι'] [nonempty ι']
  (vertices : ι' → D) (coeffs : std_simplex ℝ ι') : D :=
  ⟨finset.univ.sum (λ i, coeffs.val i • (vertices i).val), 
   convex.sum_mem hConvex (λ i _, coeffs.property.left i) coeffs.property.right
                          (λ i _, (vertices i).property)⟩

lemma convex_combination_cont {ι' : Type} [fintype ι'] [nonempty ι']
  : continuous (function.uncurry (@convex_combination ι' _ _)) := 
  have continuous (λ p : (ι' → (ι → ℝ)) × (ι' → ℝ), finset.univ.sum (λ i, p.snd i • p.fst i)),
  by { continuity, simp, continuity,
       { exact continuous.snd' (continuous_apply i_1) },
       { exact continuous.fst' (continuous_apply_apply i_1 i) } },
  (homeomorph.subtype_prod_equiv_prod.trans
    (homeomorph.Pi_to_subtype.prod_congr (homeomorph.refl _))).comp_continuous_iff'.mp
    (continuous.congr 
     (continuous.cod_restrict (this.comp continuous_subtype_val)
                              (λ p, convex.sum_mem hConvex (λ i _, p.property.right.left i)
                                                           p.property.right.right
                                                           (λ i _, p.property.left i)))
     (by { rintro ⟨p, h⟩, refl }))

noncomputable
def singular_simplex_of_vertices {n : ℕ}
  (vertices : fin (n + 1) → D)
  : topological_simplex n ⟶ Top.of D :=
  ⟨(topological_simplex_alt_desc n).to_fun, (topological_simplex_alt_desc n).continuous_to_fun⟩
  ≫ ⟨convex_combination vertices, convex_combination_cont.comp (continuous.prod.mk vertices)⟩

lemma cone_construction_lift_vertex_span {n : ℕ} (vertices : fin (n + 1) → D) (v' : D)
  : @cone_construction_lift_simplex (Top.of D) v' (hConvex.contraction v') n
                                    (singular_simplex_of_vertices vertices)
  = singular_simplex_of_vertices (fin.cons v' vertices) :=
begin
  ext x : 1,
  obtain ⟨⟨t, y⟩, h⟩ := q_surj n x,
  delta cone_construction_lift_simplex,
  transitivity, 
  apply @lift_along_quot_map_spec (Top.of (unit_interval × topological_simplex n))
                                  (topological_simplex (n + 1))
                                  (Top.of D)
                                  ⟨function.uncurry (q_map n), q_continuous n⟩ _ _ _ x (t, y) h,
  subst h, cases v' with v' hv',
  delta convex.contraction star_convex.contraction,
  apply subtype.eq, dsimp [cylinder, singular_simplex_of_vertices, convex_combination],
  rw @fin.sum_univ_succ _ _ (n + 1),
  rw finset.smul_sum,
  congr,
  ext i j, simp, rw ← mul_assoc, congr,
  dsimp [q_map, topological_simplex_alt_desc],
  split_ifs,
  { exfalso, exact fin.succ_ne_zero i h },
  { congr, change i = fin.pred_above 0 (i.succ),
    symmetry, apply fin.pred_above_succ_above, }
end

noncomputable
def barycenter (n : ℕ) : topological_simplex n :=
  ⟨(λ _, (n + 1)⁻¹), by simp [simplex_category.to_Top_obj]⟩

-- It would be a lot nicer if we did everything with topological_simplex_alt...
noncomputable
def barycenter_contraction (n : ℕ) 
  : continuous_map.homotopy (continuous_map.id (topological_simplex n))
                            (continuous_map.const _ (barycenter n)) := {
  to_fun := λ p, ⟨λ i, unit_interval.to_nnreal p.fst / (n + 1)
                     + unit_interval.to_nnreal (unit_interval.symm p.fst) * p.snd.val i,
                  by { refine eq.trans finset.sum_add_distrib _,
                       rw ← finset.mul_sum, simp,
                       transitivity unit_interval.to_nnreal p.fst
                                  + unit_interval.to_nnreal (unit_interval.symm p.fst) * 1,
                       { refine congr_arg2 _ _ (congr_arg _ p.snd.property), 
                         rw [mul_div, mul_comm, ← mul_div], simp },
                       simp [unit_interval.symm, unit_interval.to_nnreal] }⟩,
  continuous_to_fun := by { continuity,
                            refine continuous.snd' (_ : continuous (λ x : topological_simplex n, x.val i)),
                            refine continuous.congr ((continuous_apply i).comp continuous_subtype_val) _,
                            intro, refl },
  map_zero_left' := by { intro, ext, simp },
  map_one_left' := by { intro, ext, simp [barycenter] }
}


-- def barycentric_subdivision_of_standard_simplex (R : Type*) [comm_ring R]
--   : Π (n : ℕ), ((singular_chain_complex R).obj (topological_simplex n)).X n
-- | 0       := simplex_to_chain (continuous_map.id (topological_simplex 0)) R
-- | (n + 1) := cone_construction_hom R
--                                    (barycenter (n + 1)) 
--                                    ((topological_simplex_convex (n + 1)).contraction
--                                      (barycenter (n + 1)))
--                                    n
--                                    (barycentric_subdivision_of_standard_simplex n)

noncomputable
def barycentric_subdivision_in_deg (R : Type*) [comm_ring R]
  : Π (n : ℕ), (singular_chain_complex R ⋙ homological_complex.eval _ _ n)
             ⟶ (singular_chain_complex R ⋙ homological_complex.eval _ _ n)
| 0       := (singular_chain_complex_basis R 0).map_out 
               (singular_chain_complex R ⋙ homological_complex.eval _ _ 0)
               (λ _, simplex_to_chain (continuous_map.id (topological_simplex 0)) R)
| (n + 1) := (singular_chain_complex_basis R (n + 1)).map_out 
               (singular_chain_complex R ⋙ homological_complex.eval _ _ (n + 1))
               (λ _, cone_construction_hom
                       R (barycenter (n + 1))
                       (barycenter_contraction (n + 1))
                       n
                       ((barycentric_subdivision_in_deg n).app (topological_simplex (n + 1))
                          (((singular_chain_complex R).obj (topological_simplex (n + 1))).d
                            (n + 1) n
                            (simplex_to_chain (continuous_map.id (topological_simplex (n + 1))) R))))

lemma barycentric_subdivison_chain_map_step (R : Type) {X : Top} (j : ℕ) [comm_ring R] :
  (barycentric_subdivision_in_deg R (j + 1)).app X ≫
      ((singular_chain_complex R).obj X).d (j + 1) j =
    ((singular_chain_complex R).obj X).d (j + 1) j ≫
      (barycentric_subdivision_in_deg R j).app X :=
begin
  apply basis.ext ((singular_chain_complex_basis R (j + 1)).get_basis X),
  rintro ⟨_, σ⟩,
  dsimp [barycentric_subdivision_in_deg ],
  rw map_out_desc,
  simp,
  
end

noncomputable
def barycentric_subdivision (R : Type*) [comm_ring R] {X : Top}
  : singular_chain_complex R ⟶ singular_chain_complex R :=
  homological_complex_functor.mk_nat_trans
    (barycentric_subdivision_in_deg R)
    (λ i j hij X, by { dsimp at hij, subst hij, apply barycentric_subdivison_chain_map_step })

end