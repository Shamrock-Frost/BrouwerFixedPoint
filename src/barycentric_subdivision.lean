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

def singular_simplex_of_vertices {n : ℕ}
  (vertices : fin (n + 1) → D) : C(topological_simplex n, Top.of D) :=
  ⟨convex_combination vertices, convex_combination_cont.comp (continuous.prod.mk vertices)⟩.

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
                                  (Top.of (topological_simplex (n + 1)))
                                  (Top.of D)
                                  ⟨function.uncurry (q_map n), q_continuous n⟩ _ _ _ x (t, y) h,
  subst h, cases v' with v' hv',
  delta convex.contraction star_convex.contraction,
  apply subtype.eq, dsimp [cylinder, singular_simplex_of_vertices, convex_combination],
  refine (eq.trans (fin.sum_univ_succ _) _).symm,
  rw finset.smul_sum,
  congr,
  ext i j, simp, rw ← mul_assoc, congr,
  dsimp [q_map],
  split_ifs,
  { exfalso, exact fin.succ_ne_zero i h },
  { congr, exact fin.pred_above_succ_above (0 : fin (n + 1)) i }
end

lemma boundary_of_cone_construction_of_convex_contract_deg0 (R : Type*) [comm_ring R]
  (v' : D)
  (c : ((singular_chain_complex R).obj (Top.of D)).X 0)
  : ((singular_chain_complex R).obj (Top.of D)).d 1 0
      (@cone_construction_hom R _ (Top.of D)
            v'
            (hConvex.contraction v')
            0
            c)
  = c - @ε_hom R _ (Top.of D) v' 0 c :=
begin
  have := (@cone_construction R _ (Top.of D) v' (hConvex.contraction v')).comm 0,
  rw ← sub_eq_iff_eq_add at this,
  simp at this,
  symmetry,
  refine eq.trans _ (congr_fun (congr_arg coe_fn this) c),
  simp, refl
end

lemma boundary_of_cone_construction_of_convex_contract (R : Type*) [comm_ring R]
  {n : ℕ} (v' : D)
  (c : ((singular_chain_complex R).obj (Top.of D)).X (n + 1))
  : ((singular_chain_complex R).obj (Top.of D)).d (n + 2) (n + 1)
      (@cone_construction_hom R _ (Top.of D)
            v'
            (hConvex.contraction v')
            (n + 1)
            c)
  = c - (@cone_construction_hom R _ (Top.of D)
            v'
            (hConvex.contraction v')
            n
            (((singular_chain_complex R).obj (Top.of D)).d (n + 1) n c)) :=
begin
  have := congr_fun (congr_arg coe_fn ((@cone_construction R _ (Top.of D) v' (hConvex.contraction v')).comm (n + 1))) c,
  simp [ε, ε_hom, ε_map, cone_construction, cone_construction_complex_hom] at this,
  rw [@add_comm (((singular_chain_complex R).obj (Top.of D)).X (n + 1)), ← sub_eq_iff_eq_add] at this,
  exact this.symm
end

end

noncomputable
def barycenter (n : ℕ) : topological_simplex n :=
  ⟨(λ _, (n + 1)⁻¹), ⟨(λ _, inv_nonneg.mp (by { simp, exact le_of_lt (nat.cast_add_one_pos n) })),
                      by { simp [simplex_category.to_Top'_obj], apply mul_inv_cancel,
                           exact nat.cast_add_one_ne_zero n }⟩⟩

noncomputable
def barycentric_subdivision_in_deg (R : Type*) [comm_ring R]
  : Π (n : ℕ), (singular_chain_complex R ⋙ homological_complex.eval _ _ n)
             ⟶ (singular_chain_complex R ⋙ homological_complex.eval _ _ n)
| 0       := 𝟙 _
| (n + 1) := (singular_chain_complex_basis R (n + 1)).map_out 
               (singular_chain_complex R ⋙ homological_complex.eval _ _ (n + 1))
               (λ _, @cone_construction_hom R _ (Top.of (topological_simplex (n + 1)))
                       (barycenter (n + 1))
                       ((convex_std_simplex ℝ (fin (n + 2))).contraction (barycenter (n + 1)))
                       n
                       ((barycentric_subdivision_in_deg n).app (Top.of (topological_simplex (n + 1)))
                          (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 1)))).d
                            (n + 1) n
                            (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R))))

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

local attribute [instance] classical.prop_decidable

lemma simplex_category.to_Top'_map_eq_affine_map {x y : simplex_category} (f : x ⟶ y)
  : simplex_category.to_Top'.map f
  = singular_simplex_of_vertices (convex_std_simplex ℝ (fin (y.len + 1)))
                                 (λ j, vertex y.len (f j)) :=
begin
  ext p : 1, simp [simplex_category.to_Top'_map, singular_simplex_of_vertices, convex_combination],
  ext k, simp,
  rw ← @finset.sum_filter_ne_zero _ _ finset.univ,
  rw ← finset.sum_filter_ne_zero,
  apply finset.sum_congr,
  { rw finset.filter_filter, congr, 
    { ext j : 2, split; intro h,
      { rw ← h.left,
        refine ne_of_eq_of_ne (congr_arg (λ t, p.val j * t) (vertex_coord_one y.len (f j))) _,
        rw [mul_one],
        exact h.right },
      { rw mul_ne_zero_iff at h, 
        refine and.intro _ h.left,
        by_contra h', apply h.right,
        exact vertex_coord_zero y.len _ _ h' } } },
  { intros j h, replace h := (finset.mem_filter.mp h).right, 
    by_cases h' : (f j) = k,
    { rw h', symmetry,
      refine mul_right_eq_self₀.mpr _,
      left, exact vertex_coord_one y.len k },
    { exfalso, apply h,
      apply mul_eq_zero_of_right,
      exact vertex_coord_zero y.len _ _ h' } }
end

lemma barycentric_subdivison_chain_map_deg1_on_id (R : Type) [comm_ring R] :
  ((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d 1 0 
    ((barycentric_subdivision_in_deg R 1).app (Top.of (topological_simplex 1))
      (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R))
  = (barycentric_subdivision_in_deg R 0).app (Top.of (topological_simplex 1))
      (((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d 1 0
        (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R)) :=
begin
  have : ∀ n Y (τ : Top.of (topological_simplex n) ⟶ Y),
            @simplex_to_chain n (Top.to_sSet'.obj Y) τ R _
          = ((singular_chain_complex_basis R n).get_basis Y) ⟨(), τ⟩,
  { intros, dsimp [functor_basis.get_basis, simplex_to_chain], rw basis.mk_apply,
    symmetry, refine eq.trans finsupp.map_domain_single _,
    congr, apply category_theory.category.id_comp },

  transitivity ((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d 1 0 
                 (@cone_construction_hom R _ (Top.of (topological_simplex 1))
                       (barycenter 1)
                       ((convex_std_simplex ℝ (fin 2)).contraction (barycenter 1))
                       0
                       ((barycentric_subdivision_in_deg R 0).app (Top.of (topological_simplex 1))
                          (((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d
                            1 0
                            (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R)))),
  { refine congr_arg _ _,
    dsimp [barycentric_subdivision_in_deg], 
    rw this,
    rw map_out_desc,
    simp,
    rw (singular_chain_complex R).map_id (Top.of (topological_simplex 1)),
    rw homological_complex.id_f ((singular_chain_complex R).obj (Top.of (topological_simplex 1))),
    refl },
  
  rw boundary_of_cone_construction_of_convex_contract_deg0,
  rw sub_eq_self,
  dsimp [simplex_to_chain], rw singular_chain_complex_differential_desc_deg_0,
  rw [map_sub, this, this], dsimp [barycentric_subdivision_in_deg],
  rw map_sub, rw sub_eq_zero,
  simp [ε_hom, ε_map],
  rw [← this, ← this],
  rw [@category_theory.category.comp_id _ _ _ (Top.of (topological_simplex 1)),
      @category_theory.category.comp_id _ _ _ (Top.of (topological_simplex 1))],
  simp [simplex_to_chain]
end

lemma barycentric_subdivison_chain_map_deg1 (R : Type) {X : Top} [comm_ring R] :
  (barycentric_subdivision_in_deg R 1).app X ≫
      ((singular_chain_complex R).obj X).d 1 0 =
    ((singular_chain_complex R).obj X).d 1 0 ≫
      (barycentric_subdivision_in_deg R 0).app X :=
begin
  apply basis.ext ((singular_chain_complex_basis R 1).get_basis X),
  rintro ⟨i, σ⟩,
  dsimp [functor_basis.get_basis], rw basis.mk_apply,
  change ((singular_chain_complex R).obj X).d 1 0
           ((barycentric_subdivision_in_deg R 1).app X
             (((singular_chain_complex R).map σ).f 1
               (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R)))
       = (barycentric_subdivision_in_deg R 0).app X
           (((singular_chain_complex R).obj X).d (0 + 1) 0
             (((singular_chain_complex R).map σ).f 1
               (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R))),
  rw [← homological_complex.eval_map, ← category_theory.functor.comp_map,
      ← category_theory.comp_apply _ ((barycentric_subdivision_in_deg R 1).app X)],
  rw (barycentric_subdivision_in_deg R 1).naturality,
  dsimp,
  rw [← category_theory.comp_apply, ((singular_chain_complex R).map σ).comm],
  dsimp,
  refine eq.trans (congr_arg (((singular_chain_complex R).map σ).f 0) (barycentric_subdivison_chain_map_deg1_on_id R)) _,
  rw [← category_theory.comp_apply, ← homological_complex.eval_map,
      ← category_theory.functor.comp_map, ← (barycentric_subdivision_in_deg R 0).naturality],
  dsimp,
  refine congr_arg ((barycentric_subdivision_in_deg R 0).app X) _,
  rw [← category_theory.comp_apply, ← category_theory.comp_apply],
  refine congr_fun (congr_arg coe_fn _) _,
  symmetry, exact ((singular_chain_complex R).map σ).comm 1 0
end

lemma barycentric_subdivison_chain_map_degn_on_id (R : Type) [comm_ring R] (n : ℕ) :
  (∀ X, (barycentric_subdivision_in_deg R (n + 1)).app X ≫
          ((singular_chain_complex R).obj X).d (n + 1) n =
        ((singular_chain_complex R).obj X).d (n + 1) n ≫
          (barycentric_subdivision_in_deg R n).app X) →
  ((singular_chain_complex R).obj (Top.of (topological_simplex (n + 2)))).d (n + 2) (n + 1) 
    ((barycentric_subdivision_in_deg R (n + 2)).app (Top.of (topological_simplex (n + 2)))
      (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 2)))) R))
  = (barycentric_subdivision_in_deg R (n + 1)).app (Top.of (topological_simplex (n + 2)))
      (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 2)))).d (n + 2) (n + 1)
        (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 2)))) R)) :=
begin
  intro H,
  have : ∀ n Y (τ : Top.of (topological_simplex n) ⟶ Y),
            @simplex_to_chain n (Top.to_sSet'.obj Y) τ R _
          = ((singular_chain_complex_basis R n).get_basis Y) ⟨(), τ⟩,
  { intros, dsimp [functor_basis.get_basis, simplex_to_chain], rw basis.mk_apply,
    symmetry, refine eq.trans finsupp.map_domain_single _,
    congr, apply category_theory.category.id_comp },

  transitivity ((singular_chain_complex R).obj (Top.of (topological_simplex (n + 2)))).d (n + 2) (n + 1) 
                 (@cone_construction_hom R _ (Top.of (topological_simplex (n + 2)))
                       (barycenter (n + 2))
                       ((convex_std_simplex ℝ (fin (n + 3))).contraction (barycenter (n + 2)))
                       (n + 1)
                       ((barycentric_subdivision_in_deg R (n + 1)).app (Top.of (topological_simplex (n + 2)))
                          (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 2)))).d
                            (n + 2) (n + 1)
                            (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 2)))) R)))),
  { refine congr_arg _ _,
    dsimp [barycentric_subdivision_in_deg], 
    rw this (n + 2),
    rw map_out_desc,
    simp,
    rw (singular_chain_complex R).map_id (Top.of (topological_simplex (n + 2))),
    rw homological_complex.id_f ((singular_chain_complex R).obj (Top.of (topological_simplex (n + 2)))),
    refl },
  
  rw boundary_of_cone_construction_of_convex_contract,
  rw sub_eq_self,
  refine eq.trans (congr_arg _ _) (map_zero _),
  rw ← category_theory.comp_apply,
  rw H,
  rw category_theory.comp_apply,
  refine eq.trans (congr_arg _ _) (map_zero _),
  rw ← category_theory.comp_apply,
  simp
end

lemma barycentric_subdivison_chain_map_degn (R : Type) {X : Top} [comm_ring R] (n : ℕ) :
  (∀ Y, (barycentric_subdivision_in_deg R (n + 1)).app Y ≫
          ((singular_chain_complex R).obj Y).d (n + 1) n =
        ((singular_chain_complex R).obj Y).d (n + 1) n ≫
          (barycentric_subdivision_in_deg R n).app Y) →
  (barycentric_subdivision_in_deg R (n + 2)).app X ≫
          ((singular_chain_complex R).obj X).d (n + 2) (n + 1) =
        ((singular_chain_complex R).obj X).d (n + 2) (n + 1) ≫
          (barycentric_subdivision_in_deg R (n + 1)).app X :=
begin
  intro H,
  apply basis.ext ((singular_chain_complex_basis R (n + 2)).get_basis X),
  rintro ⟨i, σ⟩,
  dsimp [functor_basis.get_basis], rw basis.mk_apply,
  change ((singular_chain_complex R).obj X).d (n + 2) (n + 1)
           ((barycentric_subdivision_in_deg R (n + 2)).app X
             (((singular_chain_complex R).map σ).f (n + 2)
               (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 2)))) R)))
       = (barycentric_subdivision_in_deg R (n + 1)).app X
           (((singular_chain_complex R).obj X).d (n + 2) (n + 1)
             (((singular_chain_complex R).map σ).f (n + 2)
               (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 2)))) R))),
  rw [← homological_complex.eval_map, ← category_theory.functor.comp_map,
      ← category_theory.comp_apply _ ((barycentric_subdivision_in_deg R (n + 2)).app X)],
  rw (barycentric_subdivision_in_deg R (n + 2)).naturality,
  dsimp,
  rw [← category_theory.comp_apply, ((singular_chain_complex R).map σ).comm],
  dsimp,
  refine eq.trans (congr_arg (((singular_chain_complex R).map σ).f (n + 1)) (barycentric_subdivison_chain_map_degn_on_id R n H)) _,
  rw [← category_theory.comp_apply, ← homological_complex.eval_map,
      ← category_theory.functor.comp_map, ← (barycentric_subdivision_in_deg R (n + 1)).naturality],
  dsimp,
  refine congr_arg ((barycentric_subdivision_in_deg R (n + 1)).app X) _,
  rw [← category_theory.comp_apply, ← category_theory.comp_apply],
  refine congr_fun (congr_arg coe_fn _) _,
  symmetry, exact ((singular_chain_complex R).map σ).comm (n + 2) (n + 1)
end

lemma barycentric_subdivison_chain_map (R : Type) {X : Top} [comm_ring R] (n : ℕ)
  : (barycentric_subdivision_in_deg R (n + 1)).app X ≫
      ((singular_chain_complex R).obj X).d (n + 1) n =
    ((singular_chain_complex R).obj X).d (n + 1) n ≫
      (barycentric_subdivision_in_deg R n).app X :=
begin
  revert X, induction n; intro X,
  apply barycentric_subdivison_chain_map_deg1,
  apply barycentric_subdivison_chain_map_degn,
  assumption
end

noncomputable
def barycentric_subdivision (R : Type*) [comm_ring R]
  : singular_chain_complex R ⟶ singular_chain_complex R :=
  homological_complex_functor.mk_nat_trans
    (barycentric_subdivision_in_deg R)
    (λ i j hij X, by { dsimp at hij, subst hij, apply barycentric_subdivison_chain_map })

noncomputable
def barycentric_subdivision_homotopic_id (R : Type*) [comm_ring R]
  : natural_chain_homotopy (𝟙 (singular_chain_complex R)) (barycentric_subdivision R) := 
  @chain_complex.mk_natural_chain_homotopy_rec Top (Module R) _ _ _ _ _ _ _ 
                                               (singular_chain_complex R) (singular_chain_complex R)
                                               (𝟙 (singular_chain_complex R))
                                               (barycentric_subdivision R)
                                               0 (λ X, by { simp, refl })
                                               (λ n s _,
                                                    (singular_chain_complex_basis R (n + 1)).map_out
                                                      (singular_chain_complex R
                                                      ⋙ homological_complex.eval _ _ (n + 2))
                                                      (λ p, @cone_construction_hom R _
                                                              (Top.of (topological_simplex (n + 1)))
                                                              (barycenter (n + 1))
                                                              ((convex_std_simplex ℝ (fin (n + 2))).contraction (barycenter (n + 1)))
                                                              (n + 1)
                                                              (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R
                                                              - ((barycentric_subdivision_in_deg R _).app _ (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R))
                                                              - s.app (Top.of (topological_simplex (n + 1)))
                                                                  (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 1)))).d (n + 1) n 
                                                                    (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R)))))
                                               (by { intros,
                                                     apply basis.ext ((singular_chain_complex_basis R (n + 1)).get_basis X),
                                                     rintro ⟨i, σ⟩, cases i,
                                                     have : ∀ n Y (τ : Top.of (topological_simplex n) ⟶ Y),
                                                              @simplex_to_chain n (Top.to_sSet'.obj Y) τ R _
                                                            = ((singular_chain_complex_basis R n).get_basis Y) ⟨(), τ⟩,
                                                    { intros, dsimp [functor_basis.get_basis, simplex_to_chain], rw basis.mk_apply,
                                                      symmetry, refine eq.trans finsupp.map_domain_single _,
                                                      congr, apply category_theory.category.id_comp },
                                                     simp,
                                                     suffices H : ∀ a b c d : (((singular_chain_complex R).obj X).X (n + 1)),
                                                                  c = a - b - d → a = b + c + d,
                                                     { apply H,
                                                       rw map_out_desc, rw ← this, simp,
                                                       rw [sub_right_comm, sub_eq_iff_eq_add],
                                                       transitivity ((singular_chain_complex R).map σ).f (n + 1)
                                                                    (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 1)))).d (n + 2) (n + 1)
                                                                       (@cone_construction_hom R _
                                                                         (Top.of (topological_simplex (n + 1)))
                                                                         (barycenter (n + 1))
                                                                         ((convex_std_simplex ℝ (fin (n + 2))).contraction (barycenter (n + 1)))
                                                                         (n + 1)
                                                                         (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R
                                                                         - s.app (Top.of (topological_simplex (n + 1)))
                                                                            (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 1)))).d (n + 1) n 
                                                                              (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R))))),
                                                       rw [← category_theory.comp_apply,
                                                           ← category_theory.comp_apply (((singular_chain_complex R).map σ).f (n + 2)),
                                                           ← map_sub, ((singular_chain_complex R).map σ).comm],
                                                       dsimp,
                                                       refine congr_arg _ _,
                                                       refine congr_arg _ _,
                                                       symmetry, apply map_sub,
                                                       rw boundary_of_cone_construction_of_convex_contract,
                                                       rw map_sub (((singular_chain_complex R).obj (Top.of (topological_simplex (n + 1)))).d (n + 1) n),
                                                       specialize h (Top.of (topological_simplex (n + 1))),
                                                       simp at h,
                                                       rw ← sub_eq_iff_eq_add at h,
                                                       rw [← category_theory.comp_apply (s.app (Top.of (topological_simplex (n + 1)))),
                                                           ← category_theory.comp_apply _ (s.app (Top.of ↥(topological_simplex (n + 1))) ≫ ((singular_chain_complex R).obj (Top.of ↥(topological_simplex (n + 1)))).d (n + 1) n)],
                                                       rw ← h, simp,
                                                       rw sub_add,
                                                       apply congr_arg2,
                                                       { apply congr_arg2,
                                                         { dsimp [simplex_to_chain],
                                                           rw singular_chain_complex_map,
                                                           exact congr_fun (congr_arg finsupp.single (category_theory.category.id_comp σ)) 1, },
                                                         { dsimp [simplex_to_chain],
                                                           rw [← category_theory.comp_apply,
                                                               ← homological_complex.eval_map,
                                                               ← category_theory.functor.comp_map,
                                                               ← s.naturality,
                                                               category_theory.functor.comp_map,
                                                               homological_complex.eval_map,
                                                               category_theory.comp_apply,
                                                               ← category_theory.comp_apply _ (((singular_chain_complex R).map σ).f n)],
                                                           refine congr_arg _ _,
                                                           transitivity (((singular_chain_complex R).map σ).f (n + 1) ≫ ((singular_chain_complex R).obj X).d (n + 1) n) (finsupp.single (𝟙 (Top.of (topological_simplex (n + 1)))) 1),
                                                           { exact congr_fun (congr_arg coe_fn (((singular_chain_complex R).map σ).comm (n + 1) n).symm) _ },
                                                           refine congr_arg (((singular_chain_complex R).obj X).d (n + 1) n) _,
                                                           rw singular_chain_complex_map,
                                                           exact congr_fun (congr_arg finsupp.single (category_theory.category.id_comp σ)) 1, } },
                                                       { rw [← category_theory.comp_apply _ (((barycentric_subdivision R).app (Top.of (topological_simplex (n + 1)))).f n),
                                                             ← ((barycentric_subdivision R).app (Top.of (topological_simplex (n + 1)))).comm,
                                                             category_theory.comp_apply],
                                                         have := boundary_of_cone_construction_of_convex_contract (convex_std_simplex ℝ (fin (n + 2))) R (barycenter (n + 1))
                                                                   (((barycentric_subdivision R).app (Top.of (topological_simplex (n + 1)))).f (n + 1)
                                                                     (simplex_to_chain (𝟙 (Top.of (topological_simplex (n + 1)))) R)),
                                                         rw [eq_sub_iff_add_eq, @add_comm (((singular_chain_complex R).obj (Top.of (std_simplex ℝ (fin (n + 2))))).X (n + 1)), ← eq_sub_iff_add_eq] at this,
                                                         refine eq.trans (congr_arg (((singular_chain_complex R).map σ).f (n + 1)) this) _,
                                                         rw map_sub, apply congr_arg2,
                                                         { rw [← category_theory.comp_apply,
                                                               ← homological_complex.comp_f,
                                                               ← (barycentric_subdivision R).naturality,
                                                               homological_complex.comp_f,
                                                               category_theory.comp_apply],
                                                           refine congr_arg (((barycentric_subdivision R).app X).f (n + 1)) _, 
                                                           dsimp [simplex_to_chain],
                                                           rw singular_chain_complex_map,
                                                           exact congr_fun (congr_arg finsupp.single (category_theory.category.id_comp σ)) 1 },
                                                         { rw [← category_theory.comp_apply,
                                                               ← category_theory.comp_apply (((singular_chain_complex R).map σ).f (n + 2))],
                                                           refine congr_fun _ _,
                                                           refine congr_arg _ _,
                                                           symmetry,
                                                           exact ((singular_chain_complex R).map σ).comm (n + 2) (n + 1), } } },
                                                     { intros a b c d h,
                                                       rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq] at h,
                                                       rw ← h,
                                                       ac_refl } })
