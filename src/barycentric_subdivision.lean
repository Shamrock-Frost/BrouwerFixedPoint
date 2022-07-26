import analysis.convex.basic analysis.convex.combination topology.metric_space.basic
import data.set.finite

import .homotopy_invariance 

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

section subcomplexes_with_indexing

-- weird universe issues without being explicit :(
universes u v w p

def spanned_by_sat (R : Type*) [comm_ring R] (M : Type*) [add_comm_monoid M] [module R M]
                   {ι : Type*} (b : basis ι R M) (s : set ι)
                   : submodule R M :=
  submodule.span R (b '' { i | i ∈ s })

lemma finsupp.subtype_domain_single {α : Type*} {M : Type*} [has_zero M]
  (p : α → Prop) (a : α) (ha : p a) (m : M)
  : finsupp.subtype_domain p (finsupp.single a m) = finsupp.single ⟨a, ha⟩ m :=
begin
  rw finsupp.eq_single_iff,
  split,
  { rintros ⟨a', _⟩ h, simp at h ⊢, have h' := finsupp.single_apply_ne_zero.mp h, exact h'.left },
  { simp }
end

-- lemma finsupp.subtype_domain_desc {α : Type*} {M : Type*} [has_zero M]
--   (p : α → Prop) [decidable_pred p] (a : α) (m : M)
--   : finsupp.subtype_domain p (finsupp.single a m)
--   = if h : p a then finsupp.single ⟨a, h⟩ m else 0 :=
-- begin
--   split_ifs,
--   { exact finsupp.subtype_domain_single p a h m },
--   { rw finsupp.subtype_domain_eq_zero_iff',
--     intros x hx, apply finsupp.single_eq_of_ne,
--     intro hax, rw hax at h, contradiction }
-- end

noncomputable
def spanned_by_sat_basis (R : Type*) [comm_ring R] (M : Type*) [add_comm_monoid M] [module R M]
                         {ι : Type*} (b : basis ι R M) (s : set ι)
                         : basis s R (spanned_by_sat R M b s) := {
  repr := {
    to_fun := λ x, @finsupp.lsubtype_domain ι R R _ _ _ s (b.repr x),
    inv_fun := λ f, ⟨b.repr.inv_fun (finsupp.lmap_domain R R subtype.val f), 
                     by { dsimp [spanned_by_sat],
                          rw basis.mem_span_iff _ b _ (set.image_subset_range _ _),
                          intros i hi,
                          simp [finsupp.map_domain] at hi,
                          obtain ⟨j, h, h'⟩ := finset.exists_ne_zero_of_sum_ne_zero hi,
                          simp at h', have h'' := finsupp.single_apply_ne_zero.mp h',
                          rw h''.left,
                          exact set.mem_image_of_mem _ j.property }⟩,
    map_add' := by { rintros ⟨x, hx⟩ ⟨y, hy⟩, dsimp, repeat { rw map_add } },
    map_smul' := by { rintros r ⟨x, hx⟩, dsimp, repeat { rw map_smul } },
    left_inv := by { rintro ⟨x, hx⟩, ext, rw subtype.coe_mk,
                     suffices : set.eq_on ((((b.repr.symm : (ι →₀ R) →ₗ[R] M).comp
                                             (finsupp.lmap_domain R R subtype.val)).comp
                                             (finsupp.lsubtype_domain s)).comp
                                             (b.repr : M →ₗ[R] (ι →₀ R)))
                                          (@linear_map.id R M _ _ _)
                                          (b '' { i | i ∈ s }),
                     { exact linear_map.eq_on_span this hx },
                     rintros y ⟨i, hi, h⟩, subst h,
                     dsimp [finsupp.lsubtype_domain],
                     rw basis.repr_self,
                     rw finsupp.subtype_domain_single (λ x, x ∈ s) i hi,
                     rw finsupp.map_domain_single,
                     exact basis.repr_symm_single_one b i },
    right_inv := by { intro f, ext i,
                      dsimp [finsupp.lsubtype_domain],
                      rw linear_equiv.apply_symm_apply,
                      exact finsupp.map_domain_apply subtype.val_injective f i }
  }
}

def subcomplex_spanned_by (R : Type u) [comm_ring R] {ι' : Type} {c : complex_shape ι'}
                          (C : homological_complex (Module.{w} R) c)
                          {ι : ι' → Type p} (b : Π (i : ι'), basis (ι i) R (C.X i))
                          (s : Π (i : ι'), set (ι i))
                          (s_mono : Π i j, c.rel i j →
                            submodule.map (C.d i j) (spanned_by_sat R (C.X i) (b i) (s i))
                            ≤ spanned_by_sat R (C.X j) (b j) (s j))
                          : homological_complex (Module.{w} R) c := 
  Module.subcomplex_of_compatible_submodules C (λ i, spanned_by_sat R (C.X i) (b i) (s i))
                                                                    (by { rintros i j y ⟨x, ⟨hx, h⟩⟩,
                                                                          subst h,
                                                                          by_cases c.rel i j,
                                                                          { exact s_mono i j h (submodule.mem_map_of_mem hx) },
                                                                          { rw C.shape' i j h, simp } })

def subcomplex_spanned_by_map
  (R : Type u) [comm_ring R] {ι' : Type} {c : complex_shape ι'}
  (C1 C2 : homological_complex (Module.{w} R) c)
  (f : C1 ⟶ C2)
  {ι1 ι2 : ι' → Type p}
  (b1 : Π (i : ι'), basis (ι1 i) R (C1.X i))
  (b2 : Π (i : ι'), basis (ι2 i) R (C2.X i))
  (s1 : Π (i : ι'), set (ι1 i)) (s2 : Π (i : ι'), set (ι2 i))
  (s1_mono : Π i j, c.rel i j →
    submodule.map (C1.d i j) (spanned_by_sat R (C1.X i) (b1 i) (s1 i))
    ≤ spanned_by_sat R (C1.X j) (b1 j) (s1 j))
  (s2_mono : Π i j, c.rel i j →
    submodule.map (C2.d i j) (spanned_by_sat R (C2.X i) (b2 i) (s2 i))
    ≤ spanned_by_sat R (C2.X j) (b2 j) (s2 j))
  (hcompat : ∀ i ℓ, ℓ ∈ s1 i → f.f i (b1 i ℓ) ∈ (spanned_by_sat R (C2.X i) (b2 i) (s2 i)))
  : subcomplex_spanned_by R C1 b1 s1 s1_mono ⟶ subcomplex_spanned_by R C2 b2 s2 s2_mono := {
    f := λ i, linear_map.cod_restrict (spanned_by_sat R (C2.X i) (b2 i) (s2 i))
                                      ((f.f i).dom_restrict (spanned_by_sat R (C1.X i) (b1 i) (s1 i)))
                                      (λ x, (submodule.map_span_le (f.f i) _ _).mpr
                                              (by { rintros x ⟨ℓ, hℓ, hx⟩, subst hx,
                                                    apply hcompat, exact hℓ })
                                              (submodule.mem_map_of_mem x.property)),
    comm' := by { intros i j hij, ext, cases x,
                  dsimp [subcomplex_spanned_by, Module.subcomplex_of_compatible_submodules],
                  rw ← category_theory.comp_apply _ (f.f j),
                  rw ← f.comm' i j hij, refl }
  }

end subcomplexes_with_indexing

section subcomplexes

noncomputable
def bounded_by_submodule (R : Type*) [comm_ring R] {X : Top} (cov : set (set X)) (n : ℕ)
  : submodule R (((singular_chain_complex R).obj X).X n)
  := spanned_by_sat R (((singular_chain_complex R).obj X).X n)
                      ((singular_chain_complex_basis R n).get_basis X)
                      { p | ∃ s, s ∈ cov ∧ set.range p.2 ⊆ s }

lemma bounded_by_subcomplex_compat (R : Type) [comm_ring R] {X : Top} (cov : set (set X)) (i j : ℕ)
  : submodule.map (((singular_chain_complex R).obj X).d i j) (bounded_by_submodule R cov i)
  ≤ bounded_by_submodule R cov j :=
begin
  by_cases (j + 1 = i),
  { subst h,
    refine (submodule.map_span_le _ _ _).mpr _,
    rintros C ⟨⟨i, σ⟩, ⟨s, H, hσ⟩, h⟩, subst h, cases i,
    rw ← simplex_to_chain_is_basis,
    dsimp [simplex_to_chain],
    rw singular_chain_complex_differential_desc,
    refine submodule.sum_mem _ _,
    intros k _,
    rw zsmul_eq_smul_cast R,
    refine submodule.smul_mem _ _ _,
    refine submodule.subset_span _,
    rw simplex_to_chain_is_basis, apply set.mem_image_of_mem,
    existsi s,
    refine ⟨H, _⟩,
    refine subset_trans _ hσ,
    exact set.range_comp_subset_range _ _ },
  { rw ← complex_shape.down_rel at h, rw homological_complex.shape' _ i j h, simp, }
end

noncomputable
def bounded_by_submodule_basis (R : Type*) [comm_ring R] {X : Top} (cov : set (set X)) (n : ℕ)
  : basis { p : Σ (i : unit), Top.of (topological_simplex n) ⟶ X // ∃ s, s ∈ cov ∧ set.range p.2 ⊆ s }
          R (bounded_by_submodule R cov n) :=
  spanned_by_sat_basis R (((singular_chain_complex R).obj X).X n)
                       ((singular_chain_complex_basis R n).get_basis X)
                       { p | ∃ s, s ∈ cov ∧ set.range p.2 ⊆ s }

noncomputable
def bounded_by_subcomplex (R : Type*) [comm_ring R] {X : Top} (cov : set (set X))
  : chain_complex (Module R) ℕ :=
  @subcomplex_spanned_by R _ ℕ (complex_shape.down ℕ)
                           ((singular_chain_complex R).obj X)
                           (λ n, Σ p : unit, Top.of (topological_simplex n) ⟶ X)
                           (λ n, (singular_chain_complex_basis R n).get_basis X)
                           (λ n, λ p, ∃ s, s ∈ cov ∧ set.range p.2 ⊆ s)
                           (λ i j hij, bounded_by_subcomplex_compat R cov i j)

-- handles both intersecting a cover with a subset and refining covers!
noncomputable
def bounded_by_subcomplex_map (R : Type) [comm_ring R] {X Y : Top} (f : X ⟶ Y)
  (covX : set (set X)) (covY : set (set Y))
  (H : ∀ s, s ∈ covX → ∃ t, t ∈ covY ∧ f '' s ⊆ t)
  : bounded_by_subcomplex R covX ⟶ bounded_by_subcomplex R covY := 
  subcomplex_spanned_by_map R _ _ ((singular_chain_complex R).map f) _ _ _ _ _ _ (by {
      rintros n ⟨i, σ⟩ ⟨s, hs, hσ⟩, cases i,
      rw ← simplex_to_chain_is_basis, dsimp [simplex_to_chain],
      rw singular_chain_complex_map,
      refine submodule.subset_span _,
      refine ⟨⟨(), σ ≫ f⟩, _, _⟩,
      { obtain ⟨t, ht, hst⟩ := H s hs,
        exact ⟨t, ht, subset_trans (subset_of_eq (set.range_comp _ _))
                                   (subset_trans (set.image_subset f hσ) hst)⟩ },
      { rw ← simplex_to_chain_is_basis, refl } })

lemma bounded_by_subcomplex_eq_bounded_by_submodule (R : Type*) [comm_ring R] {X : Top}
  (cov : set (set X)) (n : ℕ)
  : (bounded_by_subcomplex R cov).X n = Module.of R (bounded_by_submodule R cov n) := rfl

lemma bounded_by_submodule_refinement (R : Type) [comm_ring R] {X : Top} (cov cov' : set (set X))
  (h : ∀ s, s ∈ cov → ∃ s', s' ∈ cov' ∧ s ⊆ s') (n : ℕ)
  : bounded_by_submodule R cov n ≤ bounded_by_submodule R cov' n :=
begin
  refine submodule.span_mono _,
  apply set.image_subset,
  rintros ⟨i, σ⟩ ⟨s, hs1, hs2⟩,
  obtain ⟨t, ht, hst⟩ := h s hs1,
  exact ⟨t, ht, subset_trans hs2 hst⟩
end

noncomputable
def bounded_diam_submodule (R : Type*) [comm_ring R] (X : Type*) [pseudo_metric_space X]
  (ε : nnreal) (n : ℕ)
  : submodule R (((singular_chain_complex R).obj (Top.of X)).X n) :=
  bounded_by_submodule R { S : set (Top.of X) | @metric.bounded X _ S ∧ @metric.diam X _ S ≤ ε } n

noncomputable
def bounded_diam_subcomplex (R : Type*) [comm_ring R] (X : Type*) [pseudo_metric_space X]
  (ε : nnreal) : chain_complex (Module R) ℕ :=
  bounded_by_subcomplex R { S : set (Top.of X) | @metric.bounded X _ S ∧ @metric.diam X _ S ≤ ε }

lemma bounded_diam_submodule_eq_bounded_diam_submodule (R : Type*) [comm_ring R] {X : Type}
  [pseudo_metric_space X] (ε : nnreal) (n : ℕ)
  : (bounded_diam_subcomplex R X ε).X n = Module.of R (bounded_diam_submodule R X ε n) := rfl

lemma bounded_diam_submodule_monotone (R : Type) [comm_ring R] {X : Type*} [pseudo_metric_space X] 
  (ε δ : nnreal) (h : ε ≤ δ) (n : ℕ)
  : bounded_diam_submodule R X ε n ≤ bounded_diam_submodule R X δ n :=
begin
  dsimp [bounded_diam_submodule],
  apply bounded_by_submodule_refinement,
  rintros s ⟨hs1, hs2⟩,
  exact ⟨s, ⟨hs1, le_trans hs2 (nnreal.coe_le_coe.mpr h)⟩, subset_refl s⟩
end

noncomputable
def subset_submodule (R : Type*) [comm_ring R] (X : Type*) [topological_space X]
  (S : set X) (n : ℕ) : submodule R (((singular_chain_complex R).obj (Top.of X)).X n) :=
  bounded_by_submodule R {S} n

noncomputable
def subset_subcomplex (R : Type*) [comm_ring R] (X : Type*) [topological_space X]
  (S : set X) : chain_complex (Module R) ℕ :=
  bounded_by_subcomplex R ({S} : set (set (Top.of X)))

lemma subset_submodule_eq_subset_submodule (R : Type*) [comm_ring R] (X : Type)
  [topological_space X] (S : set X) (n : ℕ)
  : (subset_subcomplex R X S).X n = Module.of R (subset_submodule R X S n) := rfl

lemma subset_subcomplex_monotone (R : Type*) [comm_ring R] 
  {X : Type*} [topological_space X] (S T : set X) (h : S ⊆ T) (n : ℕ) 
  : subset_submodule R X S n ≤ subset_submodule R X T n :=
begin
  dsimp [subset_submodule],
  apply bounded_by_submodule_refinement,
  simp, assumption
end

lemma subset_subcomplex_univ (R : Type*) [comm_ring R] {X : Type*} [topological_space X] (n : ℕ)
  : subset_submodule R X (@set.univ X) n = ⊤ := 
begin
  refine eq.trans _ ((singular_chain_complex_basis R n).spanning _),
  dsimp [subset_submodule, bounded_by_submodule, spanned_by_sat],
  congr,
  ext, simp, split,
  { rintro ⟨b, σ, hσ⟩, subst hσ, existsi unit.star, existsi σ,
    refine eq.trans (singular_chain_complex_map R n σ (𝟙 (Top.of (topological_simplex n)))) _,
    dsimp [singular_chain_complex_basis, functor_basis.get_basis],
    rw basis.mk_apply, dsimp [simplex_to_chain], rw singular_chain_complex_map },
  { rintros ⟨a, σ, hσ⟩, cases a, subst hσ, existsi (), existsi σ, symmetry,
    refine eq.trans (singular_chain_complex_map R n σ (𝟙 (Top.of (topological_simplex n)))) _,
    dsimp [singular_chain_complex_basis, functor_basis.get_basis],
    rw basis.mk_apply, dsimp [simplex_to_chain], rw singular_chain_complex_map }
end

-- Should probably generalize this to a statement about covers/bounds
lemma singular_chain_complex_map_subset_subcomplex (R : Type*) [comm_ring R]
  (X Y : Type*) [topological_space X] [topological_space Y]
  (S : set X) (f : C(X, Y)) (n : ℕ)
  : submodule.map ((@category_theory.functor.map _ _ _ _ (singular_chain_complex R) (Top.of X) (Top.of Y) f).f n)
                  (subset_submodule R X S n)
  ≤ subset_submodule R Y (f '' S) n :=
begin
  refine (submodule.map_span_le _ _ _).mpr _,
  rintros C ⟨⟨i, σ⟩, ⟨s, hs, hσ⟩, h'⟩, cases i, simp at hs, subst hs,
  refine submodule.subset_span _,
  refine exists.intro ⟨(), σ ≫ f⟩ _,
  simp [Top.to_sSet'], split,
  { transitivity f '' set.range σ,
    { exact subset_of_eq (set.range_comp _ _) },
    { exact set.image_subset f hσ } },
  { symmetry, rw ← h', 
    dsimp [functor_basis.get_basis], rw [basis.mk_apply, basis.mk_apply],
    dsimp [singular_chain_complex_basis, functor_basis.get_basis, simplex_to_chain],
    rw [singular_chain_complex_map, singular_chain_complex_map, singular_chain_complex_map],
    refl }
end

lemma subset_subcomplex_le_bounded_by_subcomplex (R : Type*) [comm_ring R] {X : Type*}
  [topological_space X] (cov : set (set X)) (s : set X) (hs : s ∈ cov) (n : ℕ)
  : subset_submodule R X s n ≤ bounded_by_submodule R cov n :=
begin
  dsimp [subset_submodule],
  apply bounded_by_submodule_refinement,
  simp,
  exact ⟨s, hs, subset_refl s⟩
end 

lemma metric.lebesgue_number_lemma {M : Type*} [pseudo_metric_space M] (hCompact : compact_space M)
  (cov : set (set M)) (cov_open : ∀ s, s ∈ cov → is_open s) (hcov : ⋃₀ cov = ⊤)
  (cov_nonempty : cov.nonempty) -- if M is empty this can happen!
  : ∃ δ : nnreal, 0 < δ ∧ (∀ S : set M, metric.diam S < δ → ∃ U, U ∈ cov ∧ S ⊆ U) :=
  match lebesgue_number_lemma_sUnion (is_compact_univ_iff.mpr hCompact) cov_open (set.univ_subset_iff.mpr hcov) with
  | ⟨n, H, hn⟩ := match metric.mem_uniformity_dist.mp H with 
                 | ⟨ε, ε_pos, hε⟩ := ⟨ε.to_nnreal, real.to_nnreal_pos.mpr ε_pos, λ S hS, 
                   match em S.nonempty with
                   | or.inl ⟨x, hx⟩ := match hn x (set.mem_univ x) with
                                      | ⟨U, hU, hU'⟩ := ⟨U, hU, λ y hy, hU' y (@hε x y (lt_of_le_of_lt (metric.dist_le_diam_of_mem metric.bounded_of_compact_space hx hy) (lt_of_lt_of_eq hS (real.coe_to_nnreal _ (le_of_lt ε_pos)))))⟩
                                      end
                   | or.inr h'      := match cov_nonempty with
                                       | ⟨U, hU⟩ := ⟨U, hU, λ y hy, false.elim (eq.subst (set.not_nonempty_iff_eq_empty.mp h') hy : y ∈ (∅ : set M))⟩
                                       end
                   end⟩
                 end
  end

end subcomplexes

section 

parameters {ι : Type} [fintype ι]
parameters {D : set (ι → ℝ)} (hConvex : convex ℝ D)

def convex_combination {ι' : Type} [fintype ι'] [nonempty ι']
  (vertices : ι' → D) (coeffs : std_simplex ℝ ι') : D :=
  ⟨finset.univ.sum (λ i, coeffs.val i • (vertices i).val), 
   convex.sum_mem hConvex (λ i _, coeffs.property.left i) coeffs.property.right
                          (λ i _, (vertices i).property)⟩

lemma convex_combination_partial_app_lipschitz {ι' : Type} [fintype ι'] [nonempty ι']
  (vertices : ι' → D)
  : lipschitz_with (fintype.card ι' * ∥subtype.val ∘ vertices∥₊) (convex_combination vertices) :=
begin
  rw lipschitz_with_iff_dist_le_mul, intros x y,
  rw [subtype.dist_eq, dist_eq_norm],
  simp [convex_combination],
  rw ← finset.sum_sub_distrib,
  refine le_trans (norm_sum_le _ _) _,
  convert le_of_eq_of_le (congr_arg finset.univ.sum (funext (λ i, congr_arg norm (sub_smul (x.val i) (y.val i) (vertices i).val).symm))) _,
  refine le_of_eq_of_le (congr_arg finset.univ.sum (funext (λ i, norm_smul _ _))) _,
  refine le_trans (finset.sum_le_sum (λ i _, mul_le_mul (le_refl ∥x.val i - y.val i∥) (norm_le_pi_norm (subtype.val ∘ vertices) i) (norm_nonneg _) (norm_nonneg _))
                  : finset.univ.sum (λ i, ∥x.val i - y.val i∥ * ∥(vertices i).val∥)
                  ≤ finset.univ.sum (λ i, ∥x.val i - y.val i∥ * ∥subtype.val ∘ vertices∥)) _,
  rw ← finset.sum_mul,
  rw mul_right_comm, apply mul_le_mul,
  { dsimp [fintype.card],
    convert le_of_le_of_eq _ (@finset.sum_const _ _ (@finset.univ ι' _) _ (dist x y)), simp,
    apply finset.sum_le_sum,
    intros i _,
    rw [subtype.dist_eq, ← dist_eq_norm],
    apply dist_le_pi_dist },
  { refl },
  { apply norm_nonneg },
  { apply mul_nonneg, { norm_cast, apply zero_le }, { apply dist_nonneg } }
end

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

lemma simplex_category.to_Top'_map_comp_affine
  {x y : simplex_category} (f : x ⟶ y) (vertices : y → D)
  : simplex_category.to_Top'.map f ≫ singular_simplex_of_vertices vertices
  = singular_simplex_of_vertices (λ j, vertices (f j)) :=
begin
  ext p : 1, simp [simplex_category.to_Top'_map, singular_simplex_of_vertices, convex_combination],
  ext k, simp, simp_rw finset.sum_mul,
  refine eq.trans _ 
         (@finset.sum_fiberwise_of_maps_to _ _ _ _ _ finset.univ finset.univ
                                           f (λ _ _, finset.mem_univ _)
                                           (λ t, p.val t * (vertices (f t)).val k)),
  congr, ext j,
  apply finset.sum_congr,
  { ext i, simp },
  { intros t ht, simp at ht, rw ← ht, refl }
end

noncomputable
def affine_submodule (R : Type*) [comm_ring R] (n : ℕ)
  : submodule R (((singular_chain_complex R).obj (Top.of D)).X n) :=
  spanned_by_sat R (((singular_chain_complex R).obj (Top.of D)).X n)
                 ((singular_chain_complex_basis R n).get_basis (Top.of D))
                 { σ | ∃ vs : fin (n + 1) → D, σ.2 = singular_simplex_of_vertices vs }

noncomputable
def affine_subcomplex (R : Type*) [comm_ring R] : chain_complex (Module R) ℕ :=
  subcomplex_spanned_by R ((singular_chain_complex R).obj (Top.of D))
                        (λ n, (singular_chain_complex_basis R n).get_basis (Top.of D))
                        (λ n, { σ | ∃ vs : fin (n + 1) → D, σ.2 = singular_simplex_of_vertices vs })
                        (by { intros i j h, simp at h, subst h,
                              refine (submodule.map_span_le _ _ _).mpr _,
                              rintros C ⟨⟨i, σ⟩, ⟨vs, hvs⟩, h⟩, subst h, cases i, dsimp at hvs,
                              subst hvs,
                              dsimp [singular_chain_complex_basis, functor_basis.get_basis],
                              rw [basis.mk_apply],
                              dsimp [simplex_to_chain],
                              rw [singular_chain_complex_map],
                              rw singular_chain_complex_differential_desc,
                              simp_rw zsmul_eq_smul_cast R,
                              refine submodule.sum_smul_mem _ _ _,
                              intros i _,
                              refine submodule.subset_span _,
                              refine ⟨⟨(), simplex_category.to_Top'.map (simplex_category.δ i)
                                          ≫ 𝟙 (Top.of (topological_simplex (j + 1)))
                                          ≫ singular_simplex_of_vertices vs⟩, _⟩,
                              rw basis.mk_apply,
                              split,
                              { existsi (λ j, vs (simplex_category.δ i j)),
                                simp,
                                rw @category_theory.category.id_comp Top _
                                                                     (Top.of (topological_simplex (j + 1)))
                                                                     (Top.of D)
                                                                     (singular_simplex_of_vertices vs),
                                apply simplex_category.to_Top'_map_comp_affine },
                              { apply singular_chain_complex_map } })

lemma affine_submodule_eq_affine_submodule (R : Type*) [comm_ring R] (n : ℕ)
  : (affine_subcomplex R).X n = Module.of R (affine_submodule R n) := rfl

lemma bounded_diam_subcomplex_le_cover_subcomplex 
  (hCompact : is_compact D) (R : Type*) [comm_ring R] 
  (cov : set (set D)) (cov_open : ∀ s, s ∈ cov → is_open s) (hcov : ⋃₀ cov = ⊤) 
  (cov_nonempty : cov.nonempty) (n : ℕ)
  : ∃ δ, 0 < δ ∧ bounded_diam_submodule R D δ n ≤ bounded_by_submodule R cov n :=
begin
  obtain ⟨δ, hδ, Hδ⟩ := metric.lebesgue_number_lemma (is_compact_iff_compact_space.mp hCompact) cov
                                                    cov_open hcov cov_nonempty,
  refine ⟨δ/2, nnreal.half_pos hδ, _⟩,
  refine submodule.span_le.mpr _,
  rintros C ⟨⟨i, vs⟩, ⟨s, hs, hvs⟩, H⟩, subst H, cases i,
  refine submodule.subset_span _,
  apply set.mem_image_of_mem,
  obtain ⟨U, hU, hsU⟩ := Hδ s _,
  { existsi U,
    refine ⟨hU, _⟩,
    exact subset_trans hvs hsU },
  { refine lt_of_le_of_lt hs.right _,
    rw nnreal.coe_lt_coe,
    apply nnreal.half_lt_self, symmetry, exact ne_of_lt hδ }
end

lemma finite_is_bounded {α : Type*} [hα : nonempty α] [linear_order α] {s : set α} (h : s.finite)
  : bdd_above s :=
begin
  cases h,
  by_cases h' : s.nonempty,
  { rw ← set.nonempty_coe_sort at h',
    rw ← @finset.univ_nonempty_iff _ h at h',
    refine exists.intro ((@finset.univ _ h).max' h') _,
    intros i hi,
    exact finset.le_max' (@finset.univ _ h) ⟨i, hi⟩ (@finset.mem_univ _ h _) },
  { apply hα.elim, intro a, existsi a, intros i hi, exfalso, apply h', existsi i, exact hi }
end

lemma csupr_prod {α : Type*} {β : Type*} {γ : Type*}
  [nonempty β] [nonempty γ] [conditionally_complete_lattice α]
  {f : β × γ → α} (Hbound : bdd_above (set.range f)) :
  (⨆ (x : β × γ), f x) = ⨆ (i : β) (j : γ), f (i, j) :=
begin
  obtain ⟨B, hB⟩ := Hbound, simp [upper_bounds] at hB,
  apply eq_of_forall_ge_iff, intro c,
  split, 
  { intro H, apply csupr_le, intro i, apply csupr_le, intro j, 
    rw csupr_le_iff at H, apply H,
    { existsi B, simp [upper_bounds], exact hB } },
  { intro H, apply csupr_le, rintro ⟨i, j⟩,
    rw csupr_le_iff at H, specialize H i, rw csupr_le_iff at H, exact H j,
    { existsi B, simp [upper_bounds], intros j, exact hB i j rfl },
    { existsi B, simp [upper_bounds], intro i', 
      apply csupr_le, intro j', exact hB i' j' rfl } }
end

lemma affine_simplex_dist_maximized {n : ℕ} (vertices : fin (n + 1) → D)
  (x0 : D) (p : topological_simplex n)
  : dist x0 (singular_simplex_of_vertices vertices p) ≤ ⨆ (i : fin (n + 1)), dist x0 (vertices i) :=
begin
  rw [subtype.dist_eq, dist_eq_norm],
  have : x0 = singular_simplex_of_vertices (λ _, x0) p,
  { apply subtype.eq, dsimp [singular_simplex_of_vertices, convex_combination],
    rw ← finset.sum_smul,
    refine eq.trans (one_smul _ _).symm (congr_arg2 _ _ rfl),
    exact p.property.right.symm },
  transitivity ∥finset.univ.sum (λ (i : fin (n + 1)), p.val i • (x0.val - (vertices i).val))∥,
  { apply le_of_eq, apply congr_arg,
    refine eq.trans _ (congr_arg _ (funext (λ i, (smul_sub (p.val i) x0.val (vertices i).val).symm))),
    refine eq.trans _ finset.sum_sub_distrib.symm,
    exact congr_arg2 _ (congr_arg subtype.val this) rfl, },
  { refine le_trans (norm_sum_le _ _) _,
    simp_rw [norm_smul],
    let d := ⨆ (i : fin (n + 1)), dist x0 (vertices i),
    have d_spec : ∀ j, ∥x0.val - (vertices j).val∥ ≤ d,
    { intro j,
      rw [← dist_eq_norm, subtype.val_eq_coe, subtype.val_eq_coe,
          ← subtype.dist_eq x0 (vertices j)],
      refine le_csupr _ j,
      apply finite_is_bounded, apply set.finite_range },
    convert (finset.sum_le_sum (λ i _, mul_le_mul (le_refl ∥p.val i∥) (d_spec i)
                                                  (norm_nonneg _) (norm_nonneg _))),
    rw ← finset.sum_mul,
    simp_rw [real.norm_eq_abs],
    symmetry, convert one_mul d, 
    convert p.property.right,
    ext, simp, apply p.property.left }
end

-- This should probably be used in other places
lemma apply_affine_to_vertex_eq_vertices_apply
  {n : ℕ} (vertices : fin (n + 1) → D) (i : fin (n + 1))
  : singular_simplex_of_vertices vertices (vertex n i) = vertices i :=
begin
  apply subtype.eq, simp [singular_simplex_of_vertices, convex_combination],
  refine eq.trans (finset.sum_eq_single_of_mem i (finset.mem_univ i) _) _,
  { intros b _ hb, convert zero_smul _ (vertices b).val,
    convert vertex_coord_zero n i b hb.symm },
  { convert one_smul _ (vertices i).val, convert vertex_coord_one n i }
end

lemma vertices_apply_mem_range_singular_simplex_of_vertices
  {n : ℕ} (vertices : fin (n + 1) → D) (i : fin (n + 1))
  : vertices i ∈ set.range (singular_simplex_of_vertices vertices) :=
  ⟨vertex n i, apply_affine_to_vertex_eq_vertices_apply vertices i⟩

lemma singular_simplex_of_vertices_bounded {n : ℕ} (vertices : fin (n + 1) → D)
  : @metric.bounded D _ (set.range (singular_simplex_of_vertices vertices)) :=
begin
  rw metric.bounded_range_iff,
  existsi (((n + 1 : ℝ) * ∥subtype.val ∘ vertices∥) * metric.diam (topological_simplex n)),
  intros x y,
  refine le_trans ((convex_combination_partial_app_lipschitz vertices).dist_le_mul x y) _,
  refine mul_le_mul (le_of_eq _) _ _ _,
  { simp },
  { rw subtype.dist_eq, refine metric.dist_le_diam_of_mem _ x.property y.property,
    exact bounded_std_simplex (fin (n + 1)) },
  { apply dist_nonneg },
  { apply mul_nonneg, { norm_cast, apply zero_le }, { apply norm_nonneg } }
end

lemma affine_simplex_diam {n : ℕ} (vertices : fin (n + 1) → D)
  : @metric.diam D _ (set.range (singular_simplex_of_vertices vertices))
  = ⨆ (i j : fin (n + 1)), dist (vertices i) (vertices j) :=
begin
  apply le_antisymm,
  { have : 0 ≤ ⨆ (x : fin (n + 1) × fin (n + 1)), dist (vertices x.fst) (vertices x.snd),
    { refine le_csupr_of_le _ (0, 0) _,
      exact finite_is_bounded (set.finite_range _), 
      apply dist_nonneg },
    refine le_of_le_of_eq _ (csupr_prod (finite_is_bounded (set.finite_range (λ p : fin (n + 1) × fin (n + 1), dist (vertices p.1) (vertices p.2))))),
    apply ennreal.to_real_le_of_le_of_real this,
    dsimp [emetric.diam],
    refine supr_le _, intro, refine supr_le _, rintro ⟨p, Hp⟩, subst Hp,
    refine supr_le _, intro, refine supr_le _, rintro ⟨q, Hq⟩, subst Hq,
    rw edist_le_of_real this,
    refine le_trans (affine_simplex_dist_maximized vertices (singular_simplex_of_vertices vertices p) q) _,
    refine le_of_le_of_eq _ (csupr_prod (finite_is_bounded (set.finite_range (λ p : fin (n + 1) × fin (n + 1), dist (vertices p.1) (vertices p.2))))).symm,
    apply csupr_mono,
    { apply finite_is_bounded, apply set.finite_range },
    { intro i, dsimp,
      rw dist_comm,
      exact affine_simplex_dist_maximized vertices (vertices i) p } },
  { apply csupr_le, intro i, apply csupr_le, intro j,
    apply metric.dist_le_diam_of_mem,
    { apply singular_simplex_of_vertices_bounded },
    { apply vertices_apply_mem_range_singular_simplex_of_vertices },
    { apply vertices_apply_mem_range_singular_simplex_of_vertices } }
end

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

noncomputable
def barycenter (n : ℕ) : topological_simplex n :=
  ⟨(λ _, (n + 1)⁻¹), ⟨(λ _, inv_nonneg.mp (by { simp, exact le_of_lt (nat.cast_add_one_pos n) })),
                      by { simp [simplex_category.to_Top'_obj], apply mul_inv_cancel,
                           exact nat.cast_add_one_ne_zero n }⟩⟩

noncomputable
def convex.barycenter' {n : ℕ} (vertices : fin (n + 1) → D) : D :=
  convex_combination vertices (barycenter n)

lemma barycenter_dist_vertex_bound {n : ℕ} (vertices : fin (n + 1) → D) (i : fin (n + 1))
  : dist (hConvex.barycenter' vertices) (vertices i)
  ≤ n / (n + 1) * metric.diam (set.range vertices) :=
begin
  norm_cast,
  rw [subtype.dist_eq, dist_eq_norm],
  have : vertices i = singular_simplex_of_vertices (λ _, vertices i) (barycenter n),
  { apply subtype.eq, dsimp [singular_simplex_of_vertices, convex_combination],
    rw ← finset.sum_smul,
    refine eq.trans (one_smul _ _).symm (congr_arg2 _ _ rfl),
    exact (barycenter n).property.right.symm },
  rw this,
  dsimp [convex.barycenter', singular_simplex_of_vertices, convex_combination],
  refine le_of_eq_of_le (congr_arg norm finset.sum_sub_distrib.symm) _,
  dsimp [barycenter],
  transitivity ((n + 1)⁻¹ : ℝ) * ∥finset.univ.sum (λ j : fin (n + 1), (vertices j).val - (vertices i).val)∥,
  { apply le_of_eq,
    rw ← abs_eq_self.mpr (_ : 0 ≤ (n + 1 : ℝ)),
    swap, norm_cast, apply zero_le,
    rw [← real.norm_eq_abs],
    rw ← norm_inv,
    refine eq.trans _ (norm_smul (n + 1 : ℝ)⁻¹ (finset.univ.sum (λ (j : fin (n + 1)), (vertices j).val - (vertices i).val))),
    rw finset.smul_sum,
    congr,
    ext, simp, rw mul_sub, congr;
    rw real.norm_eq_abs; norm_cast },
  { rw [div_eq_inv_mul, mul_assoc],
    refine mul_le_mul (le_refl _) _ _ _,
    { refine le_trans (norm_sum_le _ _) _,
      refine le_of_le_of_eq (@finset.sum_le_sum _ _ _ _ (λ j, if i = j then 0 else metric.diam (set.range vertices)) finset.univ _) _,
      { intros j _,
        dsimp, split_ifs,
        { subst h, simp },
        { rw [← dist_eq_norm, ← subtype.dist_eq],
          apply metric.dist_le_diam_of_mem,
          { apply metric.bounded_of_finite, apply set.finite_range },
          { apply set.mem_range_self },
          { apply set.mem_range_self } } },
      { dsimp, 
        refine eq.trans (@finset.sum_filter_of_ne _ _ finset.univ (λ j, ite (i = j) 0 (metric.diam (set.range vertices))) _ (λ j, i ≠ j) _ (λ (j : fin (n + 1)) _ hj, (ite_ne_left_iff.mp hj).left)).symm _,
        refine eq.trans (finset.sum_congr rfl (λ j hj, ite_eq_right_iff.mpr (λ h', absurd h' (finset.mem_filter.mp hj).right))) _,
        refine eq.trans (finset.sum_const _) _,
        simp,
        left,
        rw finset.filter_ne finset.univ i,
        rw finset.card_erase_of_mem (finset.mem_univ i),
        simp } },
      { apply norm_nonneg },
      { apply inv_nonneg.mpr, norm_cast, simp, } }
end

end

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

lemma barycentric_subdivision_subset (R : Type) [comm_ring R] 
  {X : Type*} [topological_space X] (S : set X) (n : ℕ)
  : submodule.map ((barycentric_subdivision_in_deg R n).app (Top.of X))
                  (subset_submodule R X S n)
  ≤ subset_submodule R X S n :=
begin
  refine (linear_map.map_span_le _ _ _).mpr _,
  rintros C ⟨⟨i, σ⟩, ⟨s, hs, hσ⟩, H⟩, subst H, cases i, simp at hs, subst hs,
  cases n with n,
  { simp [barycentric_subdivision_in_deg], apply submodule.subset_span,
    apply set.mem_image_of_mem, refine ⟨s, rfl, hσ⟩ },
  { dsimp, simp [barycentric_subdivision_in_deg],
    rw map_out_desc,
    rw simplex_to_chain_is_basis,
    dsimp,
    have := singular_chain_complex_map_subset_subcomplex R
                                                         (topological_simplex (n + 1)) 
                                                         X
                                                         set.univ σ (n + 1),
    rw [set.image_univ, subset_subcomplex_univ] at this,
    refine subset_subcomplex_monotone R _ _ hσ (n + 1) (this _),
    exact submodule.mem_map_of_mem submodule.mem_top }
end

lemma barycentric_subdivision_subset' (R : Type) [comm_ring R] (X : Type*) [topological_space X]
  (n : ℕ) (σ : C(topological_simplex n, X))
  : (barycentric_subdivision_in_deg R n).app (Top.of X) (finsupp.single σ 1)
  ∈ subset_submodule R X (set.range σ) n :=
  barycentric_subdivision_subset R _ n ⟨finsupp.single σ 1,
                                        submodule.subset_span ⟨⟨(), σ⟩, ⟨set.range σ,
                                                                       set.mem_singleton _,
                                                                       subset_of_eq rfl⟩,
                                                               eq.symm (simplex_to_chain_is_basis R n (Top.of X) σ)⟩, rfl⟩

local attribute [instance] classical.prop_decidable

lemma singular_simplex_of_vertices_eq_id {n : ℕ}
  : singular_simplex_of_vertices (convex_std_simplex ℝ (fin (n + 1))) (vertex n)
  = 𝟙 (Top.of (topological_simplex n)) :=
begin
  ext p i, simp [singular_simplex_of_vertices, convex_combination],
  simp_rw [← subtype.val_eq_coe],
  transitivity p.val i * (vertex n i).val i,
  { apply finset.sum_eq_single_of_mem _ (finset.mem_univ _),
    intros j _ hj,
    simp [vertex],
    right, simp [simplex_category.to_Top'_map, simplex_category.const],
    apply finset.sum_eq_zero,
    intros x hx, exfalso, apply hj, simp at hx, exact hx },
  { refine eq.trans _ (mul_one _), apply congr_arg, 
    exact (vertex_coord_one n i) }
end

lemma simplex_category.to_Top'_map_eq_affine_map {x y : simplex_category} (f : x ⟶ y)
  : simplex_category.to_Top'.map f
  = singular_simplex_of_vertices (convex_std_simplex ℝ (fin (y.len + 1)))
                                 (λ j, vertex y.len (f j)) :=
begin
  refine eq.trans (category_theory.category.comp_id _).symm _,
  rw (_ : 𝟙 (simplex_category.to_Top'.obj y) = 𝟙 (Top.of (topological_simplex y.len))),
  swap, refl,
  rw ← singular_simplex_of_vertices_eq_id,
  rw simplex_category.to_Top'_map_comp_affine
end

lemma cone_construction_barycentry_comp_affine_simplex (R : Type) [comm_ring R]
  {ι : Type} [fintype ι] {D : set (ι → ℝ)} (hConvex : convex ℝ D)
  {n : ℕ} (k : ℕ) (vertices : fin (n + 1) → D)
  : @cone_construction_hom R _ (Top.of (topological_simplex n)) (barycenter n) 
                           ((convex_std_simplex ℝ (fin (n + 1))).contraction (barycenter n)) k
  ≫ (@category_theory.functor.map _ _ _ _ (singular_chain_complex R)
                                  (Top.of (topological_simplex n)) _
                                  (singular_simplex_of_vertices hConvex vertices)).f (k + 1)
  = (@category_theory.functor.map _ _ _ _ (singular_chain_complex R)
                                  (Top.of (topological_simplex n)) _
                                  (singular_simplex_of_vertices hConvex vertices)).f k
  ≫ @cone_construction_hom R _ (Top.of D) (hConvex.barycenter' vertices) (hConvex.contraction (hConvex.barycenter' vertices)) k :=
begin
  apply cone_construction_hom_naturality,
  ext p i, cases p with t p,
  delta cylinder convex.barycenter' singular_simplex_of_vertices convex_combination barycenter convex.contraction star_convex.contraction,
  simp,
  rw [finset.mul_sum, finset.mul_sum],
  refine eq.trans finset.sum_add_distrib.symm _,
  congr, ext j,
  rw [right_distrib, mul_assoc, mul_assoc]
end

lemma cone_of_barycenter_sends_bounded_to_bounded (R : Type) [comm_ring R]
  {ι :  Type} [fintype ι] {D : set (ι → ℝ)} (hConvex : convex ℝ D) 
  (n : ℕ) (δ : nnreal)
  (b : D) (S : set D) (Hb : ∀ x ∈ S, dist b x ≤ δ)
  (C : bounded_diam_submodule R D δ n
     ⊓ subset_submodule R (Top.of D) (S : set (Top.of D)) n ⊓ affine_submodule hConvex R n)
  : (@cone_construction_hom R _ (Top.of D) b (hConvex.contraction b) n) C.val
    ∈ bounded_diam_submodule R D δ (n + 1) ⊓ affine_submodule hConvex R (n + 1) := 
begin
  cases C with C hC, dsimp, 
  by_cases htrivial : (1 : R) = (0 : R),
  { rw submodule.mem_inf, split;
    convert submodule.zero_mem _;
    exact eq.trans (one_smul _ _).symm (eq.trans (congr_arg2 _ htrivial rfl) (zero_smul _ _)) },
  have hnontriv : nontrivial R := ⟨⟨1, 0, htrivial⟩⟩,
  dsimp [bounded_diam_submodule, subset_submodule, affine_submodule,
         bounded_by_submodule, spanned_by_sat] at hC,
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of D))] at hC,
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R n).get_basis (Top.of D))
                                        hnontriv)] at hC,
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of D))] at hC,
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R n).get_basis (Top.of D))
                                        hnontriv)] at hC,
  dsimp [bounded_diam_submodule, bounded_by_submodule, affine_submodule, spanned_by_sat], 
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R (n+1)).get_basis (Top.of D))],
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R (n+1)).get_basis (Top.of D))
                                        hnontriv)],
  { refine (submodule.map_span_le _ _ _).mpr _ (submodule.mem_map_of_mem hC),
    rintros x ⟨⟨i, σ⟩, ⟨⟨⟨s, hs, hσ1⟩, s', hs', hσ2⟩, vs, hσ3⟩, H⟩, cases i, simp at hs', subst hs',
    rw ← simplex_to_chain_is_basis at H, subst H, dsimp at hσ3, rw hσ3,
    simp [cone_construction_hom, simplex_to_chain],
    rw cone_construction_lift_vertex_span,
    refine submodule.subset_span _,
    refine exists.intro ⟨(), singular_simplex_of_vertices hConvex (fin.cons b vs)⟩ _,
    rw ← simplex_to_chain_is_basis,
    refine and.intro _ rfl,
    simp,
    refine ⟨set.range (singular_simplex_of_vertices hConvex (fin.cons b vs)), ⟨_, _⟩, subset_of_eq rfl⟩,
    { apply singular_simplex_of_vertices_bounded },
    { rw affine_simplex_diam,
      rw csupr_le_iff,
      intro i, rw csupr_le_iff,
      intro j,
      { revert i j,
        suffices : ∀ i j : fin (n + 2), i < j → dist (@fin.cons _ (λ _, D) b vs i)
                                                     (@fin.cons _ (λ _, D) b vs j) ≤ δ,
        { intros i j,
          rcases lt_trichotomy i j with h | h | h,
          { exact this i j h },
          { subst h, simp, },
          { rw dist_comm, exact this j i h } },
        intros i j hij,
        by_cases (i = 0),
        { subst h, rw ← fin.succ_pred j (ne.symm (ne_of_lt hij)),
          simp only [fin.cons_zero, fin.cons_succ],
          apply Hb,
          rw (_ : vs (j.pred (ne.symm (ne_of_lt hij))) = σ (vertex n (j.pred (ne.symm (ne_of_lt hij))))),
          exact hσ2 (set.mem_range_self _),
          rw hσ3,
          rw apply_affine_to_vertex_eq_vertices_apply },
        { have h' : j ≠ 0,
          { symmetry, apply ne_of_lt, exact lt_trans ((fin.pos_iff_ne_zero _).mpr h) hij },
          rw [← fin.succ_pred i h, ← fin.succ_pred j h'],
          simp only [fin.cons_succ],
          refine le_trans _ hs.right,
          apply metric.dist_le_diam_of_mem hs.left;
          refine hσ1 _; dsimp; rw hσ3;
          apply vertices_apply_mem_range_singular_simplex_of_vertices } },
      { apply finite_is_bounded, apply set.finite_range },
      { apply finite_is_bounded, apply set.finite_range } } },
  all_goals { apply set.image_subset_range }  
end

lemma barycentric_subdivison_of_affine_simplex_bound_diam (R : Type) [comm_ring R]
  {ι : Type} [fintype ι] {D : set (ι → ℝ)} (hConvex : convex ℝ D)
  {n : ℕ} (vertices : fin (n + 1) → D)
  : (barycentric_subdivision_in_deg R n).app (Top.of D)
      (simplex_to_chain (singular_simplex_of_vertices hConvex vertices) R)
  ∈ bounded_diam_submodule R D ((n : nnreal)/(n + 1 : nnreal)
                               * ⟨@metric.diam D _ (set.range vertices), metric.diam_nonneg⟩) n
    ⊓ affine_submodule hConvex R n :=
begin
  induction n with n ih,
  { simp [barycentric_subdivision_in_deg, bounded_diam_subcomplex],
    split; refine submodule.subset_span _;
    rw simplex_to_chain_is_basis; apply set.mem_image_of_mem,
    { simp,
      refine ⟨set.range (singular_simplex_of_vertices hConvex vertices), ⟨_, _⟩, subset_refl _⟩,
      { apply singular_simplex_of_vertices_bounded },
      { apply le_of_eq,
        dsimp [metric.diam],
        rw emetric.diam_eq_zero_iff.mpr _, refl,
        refine set.subsingleton_of_forall_eq (singular_simplex_of_vertices hConvex vertices topological_simplex.point) _,
        rintros b ⟨p, hp⟩,
        rw ← hp, congr } },
    { exact ⟨vertices, rfl⟩ } },
  { dsimp [barycentric_subdivision_in_deg],
    rw simplex_to_chain_is_basis R (n + 1) (Top.of D) (singular_simplex_of_vertices hConvex vertices),
    rw map_out_desc,
    dsimp [simplex_to_chain], rw singular_chain_complex_differential_desc,
    rw [map_sum, map_sum, map_sum],
    refine submodule.sum_mem _ _,
    intros k _,
    rw zsmul_eq_smul_cast R,
    rw [map_smul, map_smul, map_smul],
    refine submodule.smul_mem _ _ _,
    rw ← category_theory.comp_apply, 
    rw cone_construction_barycentry_comp_affine_simplex,
    rw [category_theory.comp_apply, ← homological_complex.eval_map,
        ← category_theory.functor.comp_map],
    rw [← category_theory.comp_apply (category_theory.nat_trans.app _ _),
        ← category_theory.nat_trans.naturality],
    dsimp [simplex_to_chain], rw singular_chain_complex_map,
    have : simplex_category.to_Top'.map (simplex_category.δ k)
         ≫ 𝟙 (Top.of (topological_simplex (n + 1))) 
         = simplex_category.to_Top'.map (simplex_category.δ k) := category_theory.category.comp_id _,
    rw this, clear this,
    rw simplex_category.to_Top'_map_comp_affine,
    specialize ih (vertices ∘ simplex_category.δ k),
    have := cone_of_barycenter_sends_bounded_to_bounded R hConvex n
              (((n : nnreal) + 1) / ((n : nnreal) + 1 + 1)
              * ⟨@metric.diam D _ (set.range vertices), metric.diam_nonneg⟩)
              (hConvex.barycenter' vertices)
              (set.range (singular_simplex_of_vertices hConvex vertices))
              _
              ⟨((barycentric_subdivision_in_deg R n).app (Top.of ↥D))
                (finsupp.single (singular_simplex_of_vertices hConvex
                                (λ (j : fin (n + 1)), vertices (simplex_category.δ k j))) 1),
               _, _⟩,
    convert this,
    { rintros x ⟨w, hx⟩, subst hx,
      refine le_trans (affine_simplex_dist_maximized hConvex vertices (hConvex.barycenter' vertices) w) _,
      apply csupr_le, intro i,
      convert barycenter_dist_vertex_bound hConvex vertices i,
      simp },
    { split,
      { refine bounded_diam_submodule_monotone R _ _ _ n ih.left, 
        apply mul_le_mul,
        { rw [nnreal.div_le_iff', ← mul_div_assoc, nnreal.le_div_iff_mul_le]; norm_cast,
          linarith, exact nat.succ_ne_zero (n + 1), exact nat.succ_ne_zero n },
        { change metric.diam (set.range (vertices ∘ simplex_category.δ k)) ≤ metric.diam (set.range vertices),
          apply metric.diam_mono,
          { apply set.range_comp_subset_range },
          { apply metric.bounded_of_finite, apply set.finite_range } },
        { exact metric.diam_nonneg },
        { exact ((↑n + 1) / (↑n + 1 + 1) : nnreal).property } },
      { refine subset_subcomplex_monotone R _ _ _ n (barycentric_subdivision_subset' R _ n _),
        convert set.range_comp_subset_range (simplex_category.to_Top'.map (simplex_category.δ k))
                                            (singular_simplex_of_vertices hConvex vertices),
        symmetry,
        have := simplex_category.to_Top'_map_comp_affine hConvex (simplex_category.δ k) vertices,
        refine eq.trans _ (congr_arg _ this),
        ext, refl } },
    { exact ih.right } }
end

lemma barycentric_subdivison_map_bound_diam_subcomplex (R : Type) [comm_ring R]
  {ι : Type} [fintype ι] {D : set (ι → ℝ)} (hConvex : convex ℝ D)
  (n : ℕ) (δ : nnreal)
  : submodule.map ((barycentric_subdivision_in_deg R n).app (Top.of D))
      (bounded_diam_submodule R D δ n ⊓ affine_submodule hConvex R n)
  ≤ (bounded_diam_submodule R D ((n : nnreal)/(n + 1 : nnreal) * δ) n
    ⊓ affine_submodule hConvex R n) :=
begin
  apply @le_of_eq_of_le _ _ _
          (submodule.map ((barycentric_subdivision_in_deg R n).app (Top.of D))
                         (submodule.span R ((singular_chain_complex_basis R n).get_basis (Top.of ↥D) ''
                                            ({i : Σ (i : (singular_chain_complex_basis R n).indices),
                                                    Top.of (topological_simplex n) ⟶ Top.of D
                                                    | (∃ (s : set D), (metric.bounded s ∧ metric.diam s ≤ δ)
                                                                    ∧ set.range i.snd ⊆ s)
                                                    ∧ ∃ (vs : fin (n + 1) → D),
                                                      i.snd = singular_simplex_of_vertices hConvex vs})))),
  { by_cases htrivial : (1 : R) = (0 : R),
    { ext, split; intro; convert submodule.zero_mem _;
      exact eq.trans (one_smul _ _).symm (eq.trans (congr_arg2 _ htrivial rfl) (zero_smul _ _)) },
    have hnontriv : nontrivial R := ⟨⟨1, 0, htrivial⟩⟩,
    dsimp [bounded_diam_submodule, bounded_by_submodule, affine_submodule, spanned_by_sat],
    rw [submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of D))],
    rw [set.image_inter (@basis.injective _ R _ _ _ _
                                          ((singular_chain_complex_basis R n).get_basis (Top.of D))
                                          hnontriv)],
    refl,
    apply set.image_subset_range, apply set.image_subset_range },
  { refine (linear_map.map_span_le _ _ _).mpr _,
    rintros C ⟨⟨i, σ⟩, ⟨⟨s, ⟨hs1, hs2⟩, hs3⟩, ⟨vs, hvs⟩⟩, h⟩, cases i, subst h,
    dsimp at hvs, subst hvs,
    split,
    { refine bounded_diam_submodule_monotone R
              ((n : nnreal)/(n + 1 : nnreal) * ⟨@metric.diam D _ (set.range vs), metric.diam_nonneg⟩)
              ((n : nnreal)/(n + 1 : nnreal) * δ) _ n _,
      { apply mul_le_mul,
        { refl },
        { rw ← nnreal.coe_le_coe, refine le_trans _ hs2, dsimp,
          apply metric.diam_mono,
          { refine subset_trans _ hs3,
            rintros p ⟨i, hp⟩, subst hp,
            apply vertices_apply_mem_range_singular_simplex_of_vertices },
          { exact hs1 } },
        { exact metric.diam_nonneg },
        { simp } },
      { rw ← simplex_to_chain_is_basis,
        exact (barycentric_subdivison_of_affine_simplex_bound_diam R hConvex vs).left } },
    { rw ← simplex_to_chain_is_basis,
        exact (barycentric_subdivison_of_affine_simplex_bound_diam R hConvex vs).right } }
end

lemma barycentric_subdivison_chain_map_deg1_on_id (R : Type) [comm_ring R] :
  ((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d 1 0 
    ((barycentric_subdivision_in_deg R 1).app (Top.of (topological_simplex 1))
      (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R))
  = (barycentric_subdivision_in_deg R 0).app (Top.of (topological_simplex 1))
      (((singular_chain_complex R).obj (Top.of (topological_simplex 1))).d 1 0
        (simplex_to_chain (𝟙 (Top.of (topological_simplex 1))) R)) :=
begin
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
    rw simplex_to_chain_is_basis,
    rw map_out_desc,
    simp,
    rw (singular_chain_complex R).map_id (Top.of (topological_simplex 1)),
    rw homological_complex.id_f ((singular_chain_complex R).obj (Top.of (topological_simplex 1))),
    refl },
  
  rw boundary_of_cone_construction_of_convex_contract_deg0,
  rw sub_eq_self,
  dsimp [simplex_to_chain], rw singular_chain_complex_differential_desc_deg_0,
  rw [map_sub, simplex_to_chain_is_basis, simplex_to_chain_is_basis],
  dsimp [barycentric_subdivision_in_deg],
  rw map_sub, rw sub_eq_zero,
  simp [ε_hom, ε_map],
  rw [← simplex_to_chain_is_basis, ← simplex_to_chain_is_basis],
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
    rw simplex_to_chain_is_basis R (n + 2),
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

lemma iterated_barycentric_subdivison_of_affine_simplex_bound_diam (R : Type) [comm_ring R]
  {ι : Type} [fintype ι] {D : set (ι → ℝ)} (hConvex : convex ℝ D)
  {n : ℕ} (vertices : fin (n + 1) → D) (k : ℕ)
  : ((barycentric_subdivision_in_deg R n).app (Top.of D))^[k]
      (simplex_to_chain (singular_simplex_of_vertices hConvex vertices) R)
  ∈ bounded_diam_submodule R D (((n : nnreal)/(n + 1 : nnreal))^k
                               * ⟨@metric.diam D _ (set.range vertices), metric.diam_nonneg⟩) n
  ⊓ affine_submodule hConvex R n :=
begin
  induction k with k ih,
  { dsimp [barycentric_subdivision_in_deg],
    refine ⟨submodule.subset_span _, submodule.subset_span _⟩;
    rw simplex_to_chain_is_basis; apply set.mem_image_of_mem,
    { refine ⟨set.range (singular_simplex_of_vertices hConvex vertices), _, subset_of_eq rfl⟩,
      simp,
      split,
      { apply singular_simplex_of_vertices_bounded },
      { rw affine_simplex_diam,
        rw csupr_le_iff, intro i,
        rw csupr_le_iff, intro j,
        refine metric.dist_le_diam_of_mem _ (set.mem_range_self i) (set.mem_range_self j),
        apply metric.bounded_of_finite, apply set.finite_range,
        apply finite_is_bounded, apply set.finite_range,
        apply finite_is_bounded, apply set.finite_range } },
    { exact ⟨vertices, rfl⟩ } },
  { rw nat.iterate_succ,
    rw [pow_succ, mul_assoc],
    exact barycentric_subdivison_map_bound_diam_subcomplex R hConvex n _
                                                           (submodule.mem_map.mpr ⟨_, ih, rfl⟩) },
end

lemma nat_trans.iter_naturality {C D : Type*} [category_theory.category C]
  [category_theory.category D] [category_theory.concrete_category D] 
  (F : C ⥤ D) (η : F ⟶ F) {X Y : C} (f : X ⟶ Y) (x : F.obj X) (n : ℕ)
  : (η.app Y)^[n] (F.map f x) = F.map f ((η.app X)^[n] x) :=
begin
  induction n with n ih, { simp },
  { rw nat.iterate_succ, rw ih,
    rw ← category_theory.comp_apply,
    rw η.naturality, 
    rw category_theory.comp_apply,
    rw ← nat.iterate_succ (η.app X) }
end

structure cover (X : Type*) :=
(cov : set (set X)) (covers : ⋃₀ cov = ⊤)

def cover.pullback {X Y : Type*}
  (𝒰 : cover Y) (f : X → Y) : cover X := {
    cov := (set.preimage f) '' 𝒰.cov,
    covers := by { rw set.sUnion_image, simp_rw ← set.preimage_Union,
                   rw ← set.sUnion_eq_bUnion, rw 𝒰.covers, exact set.preimage_univ }
  }

lemma cover.pullback_by_continuous {X Y : Type*} [topological_space X] [topological_space Y]
  (𝒰 : cover Y) (hOpen : ∀ s, s ∈ 𝒰.cov → is_open s) (f : C(X, Y))
  : ∀ t, t ∈ (𝒰.pullback f).cov → is_open t :=
  by { rintros t ⟨s, hs, h⟩, subst h, refine (hOpen s hs).preimage f.continuous }

lemma bounded_by_subcomplex_map_pullback_le (R : Type) [comm_ring R] {X Y : Top}
  (𝒰 : cover Y) (f : X ⟶ Y) (n : ℕ)
  : submodule.map (((singular_chain_complex R).map f).f n)
                  (bounded_by_submodule R (𝒰.pullback f).cov n)
  ≤ bounded_by_submodule R 𝒰.cov n :=
begin
  refine (linear_map.map_span_le _ _ _).mpr _,
  rintros C ⟨⟨i, σ⟩, ⟨t, ht, hσ⟩, h⟩, subst h, cases i,
  obtain ⟨s, hs, hst⟩ := ht,
  rw ← simplex_to_chain_is_basis, dsimp [simplex_to_chain],
  rw singular_chain_complex_map,
  refine submodule.subset_span _,
  refine ⟨⟨(), σ ≫ f⟩, ⟨s, hs, _⟩, _⟩,
  { subst hst, 
    refine subset_trans (subset_of_eq (set.range_comp _ _)) _,
    exact set.image_subset_iff.mpr hσ },
  { rw ← simplex_to_chain_is_basis, refl }
end

lemma sufficient_barycentric_lands_in_cover (R : Type) [comm_ring R] {X : Top}
  (cov : set (set X)) (cov_is_open : ∀ s, s ∈ cov → is_open s) (hcov : ⋃₀ cov = ⊤) (n : ℕ)
  (C : ((singular_chain_complex R).obj X).X n)
  : ∃ k : ℕ, ((barycentric_subdivision_in_deg R n).app X) ^[k] C ∈ bounded_by_submodule R cov n :=
begin
  have : ∀ C', (∃ k : ℕ, ((barycentric_subdivision_in_deg R n).app X) ^[k] C'
                        ∈ bounded_by_submodule R cov n)
            ↔ C' ∈ ⨆ (k : ℕ), submodule.comap (((barycentric_subdivision_in_deg R n).app X)^k)
                                               (bounded_by_submodule R cov n),
  { intro C',
    rw submodule.mem_supr_of_directed, simp,
    intros i j, existsi i + j, split; intro x; simp; intro H,
    -- store brand wlog tactic
    swap, rename i temp, rename j i, rename temp j, rw add_comm j i,
    all_goals
    { induction j with j ih, 
      { exact H },
      { rw nat.add_succ, 
        rw nat.iterate_succ, revert ih,
        generalize : ((barycentric_subdivision_in_deg R n).app X)^[i + j] x  = y, intro H,
        refine submodule.mem_comap.mp _,
        refine (submodule.map_le_iff_le_comap.mp _) H,
        refine (linear_map.map_span_le _ _ _).mpr _ ,
        rintros x ⟨⟨i, σ⟩, ⟨s, hs, hσs⟩, h⟩, subst h, cases i,
        refine subset_subcomplex_le_bounded_by_subcomplex R cov s hs n _,
        refine subset_subcomplex_monotone R _ _ hσs n _,
        rw ← simplex_to_chain_is_basis,
        convert barycentric_subdivision_subset' R X n σ,
        -- the fact that we need this suggests bad design
        cases X, refl } } },
  let 𝒰 := cover.mk cov hcov,
  rw this,
  revert C,
  rw [← submodule.eq_top_iff', ← top_le_iff],
  rw ← (singular_chain_complex_basis R n).spanning X,
  rw submodule.span_le,
  rintro C ⟨i, σ, h⟩, cases i, dsimp [singular_chain_complex_basis] at σ,
  refine (this C).mp _, subst h,
  let 𝒰' :=  𝒰.pullback σ,
  have 𝒰'_is_open := 𝒰.pullback_by_continuous cov_is_open σ,
  have 𝒰'_nonempty : 𝒰'.cov.nonempty := @set.nonempty.of_sUnion_eq_univ _ ⟨vertex n 0⟩ _ 𝒰'.covers,
  obtain ⟨δ, δ_pos, hδ⟩ := @bounded_diam_subcomplex_le_cover_subcomplex (fin (n + 1)) _
                            (topological_simplex n)
                            (compact_std_simplex (fin (n + 1)))
                            R _ 𝒰'.cov 𝒰'_is_open 𝒰'.covers 𝒰'_nonempty n,
  simp_rw nat_trans.iter_naturality,
  have : (n : ℝ) / (n + 1 : ℝ) < 1,
  { rw div_lt_one_iff, left, norm_cast, simp },
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (nnreal.coe_pos.mpr δ_pos) this,
  existsi k, dsimp,
  convert bounded_by_subcomplex_map_pullback_le R 𝒰 σ n _,
  apply submodule.mem_map_of_mem,
  refine hδ _,
  convert bounded_diam_submodule_monotone R _ _ _ n
            (iterated_barycentric_subdivison_of_affine_simplex_bound_diam R (convex_std_simplex ℝ (fin (n + 1))) (vertex n) k).left,
  { dsimp [singular_chain_complex_basis], congr, symmetry, exact singular_simplex_of_vertices_eq_id },
  { have hk' : ((↑n / (↑n + 1)) ^ k : nnreal) ≤ δ,
    { apply le_of_lt,
      rw ← nnreal.coe_lt_coe,
      convert hk,
      simp, },
    rw ← mul_one ((↑n / (↑n + 1)) ^ k : nnreal) at hk',
    refine le_trans _ hk',
    apply mul_le_mul,
    { refl },
    { dsimp, apply metric.diam_le_of_forall_dist_le, simp,
      rintros p _ q _, 
      refine (dist_pi_le_iff _).mpr _, simp,
      intro i, 
      exact real.dist_le_of_mem_Icc_01 ⟨p.property.left i, topological_simplex.coord_le_one n i p⟩
                                       ⟨q.property.left i, topological_simplex.coord_le_one n i q⟩ },
    { exact metric.diam_nonneg },
    { simp, } }
end

noncomputable
def bounded_by_subcomplex_inclusion (R : Type) [comm_ring R] {X : Top} (cov : set (set X))
  : bounded_by_subcomplex R cov ⟶ (singular_chain_complex R).obj X :=
  Module.subcomplex_of_compatible_submodules_inclusion ((singular_chain_complex R).obj X)
    (λ n, spanned_by_sat R (((singular_chain_complex R).obj X).X n)
          (((singular_chain_complex_basis R n).get_basis X))
          { p | ∃ s, s ∈ cov ∧ set.range p.2 ⊆ s })
    (by { rintros i j y ⟨x, ⟨hx, h⟩⟩,
          subst h,
          by_cases (complex_shape.down ℕ).rel i j,
          { exact bounded_by_subcomplex_compat R cov i j (submodule.mem_map_of_mem hx) },
          { rw homological_complex.shape' _ i j h, simp } })

lemma cover_subcomplex_inclusion_quasi_iso
  (R : Type) [comm_ring R] {X : Top}
  (cov : set (set X)) (cov_is_open : ∀ s, s ∈ cov → is_open s) (hcov : ⋃₀ cov = ⊤)
  : quasi_iso (bounded_by_subcomplex_inclusion R cov) :=
begin
  dsimp [bounded_by_subcomplex_inclusion], 
  apply subcomplex_inclusion_quasi_iso_of_pseudo_projection _ _
          ((barycentric_subdivision R).app X)
          ((barycentric_subdivision_homotopic_id R).to_chain_htpy X),
  { apply sufficient_barycentric_lands_in_cover; assumption },
  { intro i,
    refine (submodule.map_span_le _ _ _).mpr _,
    rintros C ⟨⟨i, σ⟩, ⟨s, H, hσ⟩, h⟩, subst h, cases i,
    rw ← simplex_to_chain_is_basis, 
    simp [barycentric_subdivision,
          homological_complex_functor.mk_nat_trans],
    cases i with i,
    { refine submodule.subset_span _,
      rw simplex_to_chain_is_basis,
      refine set.mem_image_of_mem _ ⟨s, H, hσ⟩ },
    { change (barycentric_subdivision_in_deg R (i+1)).app X (simplex_to_chain σ R)
           ∈ bounded_by_submodule R cov (i+1),
      rw simplex_to_chain_is_basis,
      dsimp [barycentric_subdivision_in_deg],
      rw map_out_desc,
      simp,
      have := bounded_by_subcomplex_map_pullback_le R ⟨cov, hcov⟩ σ (i + 1),
      refine this (submodule.mem_map_of_mem _), clear this,
      refine subset_subcomplex_le_bounded_by_subcomplex R _ set.univ _ (i + 1) _,
      { existsi s,
        refine ⟨H, _⟩,
        rw ← set.univ_subset_iff,
        exact subset_trans (subset_of_eq (set.preimage_range _).symm) (set.preimage_mono hσ) },
      { rw subset_subcomplex_univ, simp } } },
  { intros i j, 
    by_cases (i + 1 = j),
    { subst h,
      refine (submodule.map_span_le _ _ _).mpr _,
      rintros C ⟨⟨i, σ⟩, ⟨s, H, hσ⟩, h⟩, subst h, cases i,
      dsimp [barycentric_subdivision_homotopic_id, chain_complex.mk_natural_chain_homotopy_rec],
      delta chain_complex.mk_natural_chain_homotopy,
      unfold_projs, 
      dsimp,
      split_ifs, swap, contradiction,
      cases i with i,
      { simp, },
      { simp,
        rw map_out_desc,
        have := bounded_by_subcomplex_map_pullback_le R ⟨cov, hcov⟩ σ (i + 2),
        refine this (submodule.mem_map_of_mem _), clear this,
        refine subset_subcomplex_le_bounded_by_subcomplex R _ set.univ _ (i + 2) _,
        { existsi s,
          refine ⟨H, _⟩,
          rw ← set.univ_subset_iff,
          exact subset_trans (subset_of_eq (set.preimage_range _).symm) (set.preimage_mono hσ) },
        { rw subset_subcomplex_univ, simp } } },
    { rw ← complex_shape.down_rel at h, rw homotopy.zero' _ i j h, simp } }
end

lemma cover_inclusion_natural (R : Type) [comm_ring R] {X Y : Top} (f : X ⟶ Y)
  (covX : set (set X)) (covY : set (set Y)) (H : ∀ s, s ∈ covX → ∃ t, t ∈ covY ∧ f '' s ⊆ t)
  : bounded_by_subcomplex_inclusion R covX ≫ (singular_chain_complex R).map f
  = bounded_by_subcomplex_map R f covX covY H ≫ bounded_by_subcomplex_inclusion R covY :=
begin
  ext n : 2,
  apply basis.ext (bounded_by_submodule_basis R covX n),
  rintro ⟨⟨i, σ⟩, s, hs, hσ⟩, cases i,
  simp only [bounded_by_submodule_basis, spanned_by_sat_basis,
         bounded_by_subcomplex_map, subcomplex_spanned_by_map,
         bounded_by_subcomplex_inclusion,
         Module.subcomplex_of_compatible_submodules_inclusion,
         subcomplex_spanned_by_map.equations._eqn_1,
         linear_equiv.coe_symm_mk,
         bounded_by_submodule_basis.equations._eqn_1,
         homological_complex.comp_f,
         bounded_by_subcomplex_inclusion.equations._eqn_1,
         submodule.coe_mk,
         eq_self_iff_true,
         function.comp_app,
         one_smul,
         finsupp.total_single,
         basis.coe_of_repr,
         Module.subcomplex_of_compatible_submodules_inclusion.equations._eqn_1,
         finsupp.map_domain_single,
         submodule.coe_subtype,
         spanned_by_sat_basis.equations._eqn_1,
         bounded_by_subcomplex_map.equations._eqn_1,
         Module.coe_comp,
         linear_map.cod_restrict_apply,
         linear_map.dom_restrict_apply]
end