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
def spanned_by_sat_basis (R : Type u) [comm_ring R] (M : Type w) [add_comm_monoid M] [module R M]
                         {ι : Type p} (b : basis ι R M) (s : set ι)
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

lemma spanned_by_sat_basis_apply (R : Type*) [comm_ring R] (M : Type*) [add_comm_monoid M] [module R M]
                                 {ι : Type p} (b : basis ι R M) (s : set ι)
                                 (i : ι) (hi : i ∈ s)
                                 : spanned_by_sat_basis R M b s ⟨i, hi⟩
                                 = ⟨b i, submodule.subset_span (set.mem_image_of_mem b hi)⟩ :=
begin
  apply subtype.eq, simp [spanned_by_sat_basis]
end

def subcomplex_spanned_by (R : Type u) [comm_ring R] {ι' : Type*} {c : complex_shape ι'}
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
  (R : Type u) [comm_ring R] {ι' : Type*} {c : complex_shape ι'}
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
  }.

def subcomplex_spanned_by_map_inj
  (R : Type u) [comm_ring R] {ι' : Type*} {c : complex_shape ι'}
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
  (hinj : ∀ n, function.injective (f.f n))
  : ∀ n, function.injective ((subcomplex_spanned_by_map R C1 C2 f b1 b2 s1 s2 s1_mono s2_mono hcompat).f n) :=
begin
  rintros n ⟨x, hx⟩ ⟨y, hy⟩ hxy,
  apply subtype.eq, change x = y,
  refine @hinj n x y _,
  have := congr_arg subtype.val hxy,
  exact this
end

def subcomplex_spanned_by_map_comp
  (R : Type u) [comm_ring R] {ι' : Type*} {c : complex_shape ι'}
  (C1 C2 C3 : homological_complex (Module.{w} R) c)
  (f : C1 ⟶ C2) (g : C2 ⟶ C3) 
  {ι1 ι2 ι3 : ι' → Type p}
  (b1 : Π (i : ι'), basis (ι1 i) R (C1.X i))
  (b2 : Π (i : ι'), basis (ι2 i) R (C2.X i))
  (b3 : Π (i : ι'), basis (ι3 i) R (C3.X i))
  (s1 : Π (i : ι'), set (ι1 i)) (s2 : Π (i : ι'), set (ι2 i)) (s3 : Π (i : ι'), set (ι3 i))
  (s1_mono : Π i j, c.rel i j →
    submodule.map (C1.d i j) (spanned_by_sat R (C1.X i) (b1 i) (s1 i))
    ≤ spanned_by_sat R (C1.X j) (b1 j) (s1 j))
  (s2_mono : Π i j, c.rel i j →
    submodule.map (C2.d i j) (spanned_by_sat R (C2.X i) (b2 i) (s2 i))
    ≤ spanned_by_sat R (C2.X j) (b2 j) (s2 j))
  (s3_mono : Π i j, c.rel i j →
    submodule.map (C3.d i j) (spanned_by_sat R (C3.X i) (b3 i) (s3 i))
    ≤ spanned_by_sat R (C3.X j) (b3 j) (s3 j))
  (h12 : ∀ i ℓ, ℓ ∈ s1 i → f.f i (b1 i ℓ) ∈ (spanned_by_sat R (C2.X i) (b2 i) (s2 i)))
  (h23 : ∀ i ℓ, ℓ ∈ s2 i → g.f i (b2 i ℓ) ∈ (spanned_by_sat R (C3.X i) (b3 i) (s3 i)))
  : subcomplex_spanned_by_map R C1 C2 f b1 b2 s1 s2 s1_mono s2_mono h12 
  ≫ subcomplex_spanned_by_map R C2 C3 g b2 b3 s2 s3 s2_mono s3_mono h23
  = subcomplex_spanned_by_map R C1 C3 (f ≫ g) b1 b3 s1 s3 s1_mono s3_mono
                              (λ i ℓ hℓ, (submodule.map_span_le (g.f i) _ (spanned_by_sat R (C3.X i) (b3 i) (s3 i))).mpr
                                           (λ y (hy : y ∈ (b2 i) '' (s2 i)), exists.elim hy (λ m hm, eq.subst hm.right (h23 i m hm.left)))
                                           (set.mem_image_of_mem _ (h12 i ℓ hℓ))
                              : ∀ i ℓ, ℓ ∈ s1 i → g.f i (f.f i (b1 i ℓ))
                                                 ∈ (spanned_by_sat R (C3.X i) (b3 i) (s3 i))) :=
begin
  ext n : 2, 
  apply basis.ext (spanned_by_sat_basis R (C1.X n) (b1 n) (s1 n)),
  rintro ⟨i, hi⟩,
  rw spanned_by_sat_basis_apply,
  apply subtype.eq,
  refl,
end

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

lemma bounded_by_subcomplex_map_comp (R : Type) [comm_ring R] {X Y Z : Top}
  (f : X ⟶ Y) (g : Y ⟶ Z) (covX : set (set X)) (covY : set (set Y)) (covZ : set (set Z))
  (H  : ∀ s, s ∈ covX → ∃ t, t ∈ covY ∧ f '' s ⊆ t)
  (H' : ∀ t, t ∈ covY → ∃ u, u ∈ covZ ∧ g '' t ⊆ u)
  : bounded_by_subcomplex_map R f covX covY H ≫ bounded_by_subcomplex_map R g covY covZ H'
  = bounded_by_subcomplex_map R (f ≫ g) covX covZ (λ s hs, exists.elim (H s hs) (λ t ht,
    exists.elim (H' t ht.left) (λ u hu, ⟨u, hu.left, subset_trans (subset_of_eq (set.image_comp g f s))
                                                                 (subset_trans (set.image_subset g ht.right) hu.right)⟩))) :=
begin
  delta bounded_by_subcomplex_map,
  rw subcomplex_spanned_by_map_comp,
  congr,
  symmetry, apply (singular_chain_complex R).map_comp
end

lemma bounded_by_subcomplex_map_mono (R : Type) [comm_ring R] {X Y : Top}
  (f : X ⟶ Y) (hf : function.injective f) (covX : set (set X)) (covY : set (set Y))
  (H  : ∀ s, s ∈ covX → ∃ t, t ∈ covY ∧ f '' s ⊆ t)
  : category_theory.mono (bounded_by_subcomplex_map R f covX covY H) :=
begin
  apply_with homological_complex.mono_of_eval {instances := ff},
  intro, rw Module.mono_iff_injective,
  delta bounded_by_subcomplex_map, apply subcomplex_spanned_by_map_inj,
  apply singular_chain_complex_map_inj,
  exact hf
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
    rw [← real.dist_eq, subtype.dist_eq],
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
    ext, simp, rw mul_sub, congr; norm_cast },
  { rw [div_eq_inv_mul, mul_assoc],
    refine mul_le_mul _ _ _ _,
    { norm_cast },
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
  { split;
    convert submodule.zero_mem _;
    exact eq.trans (one_smul _ _).symm (eq.trans (congr_arg2 _ htrivial rfl) (zero_smul _ _)) },
  have hnontriv : nontrivial R := ⟨⟨1, 0, htrivial⟩⟩,
  dsimp [bounded_diam_submodule, subset_submodule, affine_submodule,
         bounded_by_submodule, spanned_by_sat] at hC,
  rw [← submodule.mem_inf, ← submodule.mem_inf] at hC,
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of D))] at hC,
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R n).get_basis (Top.of D))
                                        hnontriv)] at hC,
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of D))] at hC,
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R n).get_basis (Top.of D))
                                        hnontriv)] at hC,
  dsimp [bounded_diam_submodule, bounded_by_submodule, affine_submodule, spanned_by_sat], 
  rw ← submodule.mem_inf,
  rw [submodule.inf_spans_free R ((singular_chain_complex_basis R (n+1)).get_basis (Top.of D))],
  rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R (n+1)).get_basis (Top.of D))
                                        hnontriv)],
  { refine (submodule.map_span_le _ _ _).mpr _ (submodule.mem_map_of_mem hC),
    rintros x ⟨⟨i, σ⟩, ⟨⟨⟨s, hs, hσ1⟩, s', hs', hσ2⟩, vs, hσ3⟩, H⟩, cases i, subst hs',
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
    rw ← submodule.mem_inf,
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
    rw ← submodule.mem_inf,
    convert this,
    { norm_cast }, { norm_cast },
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

def pullback_family_of_sets {X Y : Type*} (cov : set (set Y)) (f : X → Y) := (set.preimage f) '' cov

lemma pullback_family_of_sets_covers {X Y : Type*} (cov : set (set Y)) (f : X → Y)
  (hcov : ⋃₀ cov = ⊤) : ⋃₀ (pullback_family_of_sets cov f) = ⊤ :=
begin
  delta pullback_family_of_sets,
  rw set.sUnion_image, simp_rw ← set.preimage_Union,
  rw ← set.sUnion_eq_bUnion, rw hcov, exact set.preimage_univ
end

lemma pullback_family_of_sets_by_continuous {X Y : Type*}
  [topological_space X] [topological_space Y] (cov : set (set Y))
  (hOpen : ∀ s, s ∈ cov → is_open s) (f : C(X, Y))
  : ∀ t, t ∈ pullback_family_of_sets cov f → is_open t :=
  by { rintros t ⟨s, hs, h⟩, subst h, refine (hOpen s hs).preimage f.continuous }

lemma bounded_by_subcomplex_map_pullback_le (R : Type) [comm_ring R] {X Y : Top}
  (cov : set (set Y)) (f : X ⟶ Y) (n : ℕ)
  : submodule.map (((singular_chain_complex R).map f).f n)
                  (bounded_by_submodule R (pullback_family_of_sets cov f) n)
  ≤ bounded_by_submodule R cov n :=
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
  rw this,
  revert C,
  rw [← submodule.eq_top_iff', ← top_le_iff],
  rw ← (singular_chain_complex_basis R n).spanning X,
  rw submodule.span_le,
  rintro C ⟨i, σ, h⟩, cases i, dsimp [singular_chain_complex_basis] at σ,
  refine (this C).mp _, subst h,
  let cov' :=  pullback_family_of_sets cov σ,
  have cov'_is_open := pullback_family_of_sets_by_continuous cov cov_is_open σ,
  have hcov' := pullback_family_of_sets_covers cov σ hcov,
  have cov'_nonempty : cov'.nonempty := @set.nonempty.of_sUnion_eq_univ _ ⟨vertex n 0⟩ _ hcov',
  obtain ⟨δ, δ_pos, hδ⟩ := @bounded_diam_subcomplex_le_cover_subcomplex (fin (n + 1)) _
                            (topological_simplex n)
                            (compact_std_simplex (fin (n + 1)))
                            R _ cov' cov'_is_open hcov' cov'_nonempty n,
  simp_rw nat_trans.iter_naturality,
  have : (n : ℝ) / (n + 1 : ℝ) < 1,
  { rw div_lt_one_iff, left, norm_cast, simp },
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (nnreal.coe_pos.mpr δ_pos) this,
  existsi k, dsimp,
  convert bounded_by_subcomplex_map_pullback_le R cov σ n _,
  apply submodule.mem_map_of_mem,
  refine hδ _,
  convert bounded_diam_submodule_monotone R _ _ _ n
            (iterated_barycentric_subdivison_of_affine_simplex_bound_diam R (convex_std_simplex ℝ (fin (n + 1))) (vertex n) k).left,
  { dsimp [singular_chain_complex_basis], congr, symmetry, exact singular_simplex_of_vertices_eq_id },
  { have hk' : ((↑n / (↑n + 1)) ^ k : nnreal) ≤ δ,
    { apply le_of_lt,
      rw ← nnreal.coe_lt_coe,
      convert hk },
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

-- This does typecheck but it takes forever... why???
lemma subdivision_chain_homotopy_of_bounded_is_bounded
  (R : Type) [comm_ring R] {X : Top}
  (cov : set (set X)) (n : ℕ) (s : set X) (H : s ∈ cov)
  (σ : Top.of (topological_simplex n) ⟶ X) (hσ : set.range σ ⊆ s)
  : ((barycentric_subdivision_homotopic_id R).to_chain_htpy X).hom n (n+1) (simplex_to_chain σ R)
  ∈ bounded_by_submodule R cov (n + 1) :=
begin
  rw simplex_to_chain_is_basis,
  dsimp [barycentric_subdivision_homotopic_id, chain_complex.mk_natural_chain_homotopy_rec],
  delta chain_complex.mk_natural_chain_homotopy,
  unfold_projs, 
  dsimp,
  split_ifs, swap, contradiction,
  cases n with n,
  { exact submodule.zero_mem _ },
  { dsimp,
    rw map_out_desc,
    dsimp,
    refine bounded_by_subcomplex_map_pullback_le R cov σ (n.succ + 1) 
                                                   (submodule.mem_map_of_mem _), 
    convert submodule.mem_top,
    rw eq_top_iff,
    rw ← subset_subcomplex_univ,
    apply subset_subcomplex_le_bounded_by_subcomplex R (pullback_family_of_sets cov σ),
    dsimp [pullback_family_of_sets],
    refine ⟨s, H, _⟩,
    rw ← set.univ_subset_iff,
    rw ← set.preimage_range σ,
    exact set.preimage_mono hσ }
end

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
      have := bounded_by_subcomplex_map_pullback_le R cov σ (i + 1),
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
      change ((barycentric_subdivision_homotopic_id R).to_chain_htpy X).hom i (i + 1)
               ((singular_chain_complex_basis R i).get_basis X ⟨(), σ⟩)
             ∈ bounded_by_submodule R cov (i + 1),
      rw ← simplex_to_chain_is_basis,
      exact subdivision_chain_homotopy_of_bounded_is_bounded R cov i s H σ hσ },
    { rw ← complex_shape.down_rel at h, rw homotopy.zero' _ i j h, 
      rw submodule.map_zero, 
      exact bot_le } }
end

lemma cover_inclusion_natural (R : Type) [comm_ring R] {X Y : Top} (f : X ⟶ Y)
  (covX : set (set X)) (covY : set (set Y)) (H : ∀ s, s ∈ covX → ∃ t, t ∈ covY ∧ f '' s ⊆ t)
  : bounded_by_subcomplex_inclusion R covX ≫ (singular_chain_complex R).map f
  = bounded_by_subcomplex_map R f covX covY H ≫ bounded_by_subcomplex_inclusion R covY :=
begin
  ext n : 2,
  apply basis.ext (bounded_by_submodule_basis R covX n),
  rintro ⟨⟨i, σ⟩, s, hs, hσ⟩, cases i,
  delta bounded_by_submodule_basis,
  rw spanned_by_sat_basis_apply,
  refl
end

noncomputable
def bounded_by_pullback_chain_inclusion (R : Type) [comm_ring R] 
  (i : category_theory.arrow Top) (cov : set (set i.right))
  : bounded_by_subcomplex R (pullback_family_of_sets cov (i.hom)) ⟶ bounded_by_subcomplex R cov :=
  bounded_by_subcomplex_map R i.hom (pullback_family_of_sets cov i.hom)
                                                                     cov
                                                                     (λ s hs, exists.elim hs (λ t ht, ⟨t, ht.left, 
  subset_trans (set.image_subset _ (subset_of_eq ht.right.symm)) (set.image_preimage_subset _ _)⟩)).

lemma pullback_of_refinement_is_refinement (R : Type) [comm_ring R]
  {X A Y B : Top} (i : A ⟶ X) (j : B ⟶ Y)
  (g : A ⟶ B) (f : X ⟶ Y) (w : g ≫ j = i ≫ f)
  (cov : set (set X)) (cov' : set (set Y)) (H : ∀ S, S ∈ cov → ∃ T, T ∈ cov' ∧ f '' S ⊆ T)
  : ∀ s, s ∈ pullback_family_of_sets cov i → ∃ t, t ∈ pullback_family_of_sets cov' j ∧ g '' s ⊆ t :=
begin
  rintros s ⟨S, hS, hs⟩,
  obtain ⟨T, hT⟩ := H S hS,
  refine ⟨j ⁻¹' T, set.mem_image_of_mem _ hT.left, _⟩, 
  refine set.image_subset_iff.mp _,
  refine subset_trans _ hT.right,
  rw [← set.image_comp, ← hs],
  change (g ≫ j) '' (i ⁻¹' S) ⊆ f '' S,
  rw w,  refine subset_trans (subset_of_eq (set.image_comp f i _)) _,
  dsimp, 
  refine set.image_subset _ _,
  exact set.image_preimage_subset _ _ 
end

lemma bounded_by_pullback_chain_inclusion_natural(R : Type) [comm_ring R] 
  (i : category_theory.arrow Top) (j : category_theory.arrow Top) (w : i ⟶ j)
  (cov : set (set i.right)) (cov' : set (set j.right))
  (H : ∀ S, S ∈ cov → ∃ T, T ∈ cov' ∧ w.right '' S ⊆ T)
  : bounded_by_subcomplex_map R w.left (pullback_family_of_sets cov  i.hom)
                                       (pullback_family_of_sets cov' j.hom)
                                       (pullback_of_refinement_is_refinement R i.hom j.hom w.left 
                                                                             w.right w.w cov cov' H)
    ≫ bounded_by_pullback_chain_inclusion R j cov'
    = bounded_by_pullback_chain_inclusion R i cov ≫ bounded_by_subcomplex_map R w.right cov cov' H :=
begin
  delta bounded_by_pullback_chain_inclusion,
  rw [bounded_by_subcomplex_map_comp, bounded_by_subcomplex_map_comp],
  have := w.w, dsimp at this, simp_rw this,
  refl
end

noncomputable
def singular_chain_complex_of_pair_under_cover (R : Type) [comm_ring R] 
  (i : category_theory.arrow Top) (cov : set (set i.right)) : chain_complex (Module R) ℕ :=
  category_theory.limits.cokernel (bounded_by_pullback_chain_inclusion R i cov).

noncomputable
def singular_chain_complex_of_pair_under_cover_map (R : Type) [comm_ring R] 
  {i j : category_theory.arrow Top} (w : i ⟶ j)
  (cov : set (set i.right)) (cov' : set (set j.right)) 
  (H : ∀ s, s ∈ cov → ∃ t, t ∈ cov' ∧ w.right '' s ⊆ t)
  : singular_chain_complex_of_pair_under_cover R i cov
  ⟶ singular_chain_complex_of_pair_under_cover R j cov' :=
  (coker_functor (chain_complex (Module R) ℕ)).map
    (category_theory.arrow.hom_mk (bounded_by_pullback_chain_inclusion_natural R i j w cov cov' H)
    : category_theory.arrow.mk (bounded_by_pullback_chain_inclusion R i cov)
    ⟶ category_theory.arrow.mk (bounded_by_pullback_chain_inclusion R j cov'))

noncomputable
def singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair 
  (R : Type) [comm_ring R] (i : category_theory.arrow Top) (cov : set (set i.right))
  : singular_chain_complex_of_pair_under_cover R i cov ⟶ (singular_chain_complex_of_pair R).obj i :=
  (coker_functor (chain_complex (Module R) ℕ)).map
    (category_theory.arrow.hom_mk (cover_inclusion_natural R i.hom
                                    (pullback_family_of_sets cov i.hom) cov
                                    (λ s hs, exists.elim hs (λ t ht, ⟨t, ht.left, 
                                    subset_trans (set.image_subset _ (subset_of_eq ht.right.symm))
                                                 (set.image_preimage_subset _ _)⟩)))
    : category_theory.arrow.mk _ ⟶ category_theory.arrow.mk _)

lemma singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair_naturality
  (R : Type) [comm_ring R] {i j : category_theory.arrow Top} (w : i ⟶ j)
  (cov : set (set i.right)) (cov' : set (set j.right)) 
  (H : ∀ s, s ∈ cov → ∃ t, t ∈ cov' ∧ w.right '' s ⊆ t)
  : singular_chain_complex_of_pair_under_cover_map R w cov cov' H
  ≫ singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair R j cov'
  = singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair R i cov
  ≫ (singular_chain_complex_of_pair R).map w :=
begin
  dsimp [singular_chain_complex_of_pair, singular_chain_complex_of_pair_under_cover_map,
         singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair],
  rw [← (coker_functor (chain_complex (Module R) ℕ)).map_comp,
      ← (coker_functor (chain_complex (Module R) ℕ)).map_comp],
  refine congr_arg _ _,
  ext : 1; dsimp; symmetry; apply cover_inclusion_natural,
end

noncomputable
def singular_homology_of_pair_under_cover (R : Type) [comm_ring R] 
  (i : category_theory.arrow Top) (cov : set (set i.right)) (n : ℕ) : Module R := 
  (singular_chain_complex_of_pair_under_cover R i cov).homology n

lemma singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair_quasi_iso
  (R : Type) [comm_ring R] (i : category_theory.arrow Top) (hi : function.injective i.hom)
  (cov : set (set i.right)) (cov_is_open : ∀ s, s ∈ cov → is_open s) (hcov : ⋃₀ cov = ⊤)
  : quasi_iso (singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair R i cov) :=
begin
  apply coker_of_quasi_isos_between_monic_arrows_is_quasi_iso,
  { apply bounded_by_subcomplex_map_mono, exact hi },
  { apply_with homological_complex.mono_of_eval {instances := ff},
    intro, rw Module.mono_iff_injective,
    apply singular_chain_complex_map_inj, exact hi },
  { apply cover_subcomplex_inclusion_quasi_iso,
    { apply pullback_family_of_sets_by_continuous, assumption },
    { apply pullback_family_of_sets_covers, assumption } },
  { apply cover_subcomplex_inclusion_quasi_iso; assumption }
end.

def excision_inner_map {X : Type*} [topological_space X] (A B : set X)
  : Top.of (A ∩ B : set X) ⟶ Top.of A := ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩

def excision_outer_map {X : Type*} [topological_space X] (A B : set X)
  : Top.of B ⟶ Top.of X := ⟨_, continuous_subtype_val⟩

def excision_include {X : Type*} [topological_space X] (A : set X)
  : Top.of A ⟶ Top.of X := ⟨_, continuous_subtype_val⟩

def excision_include_inter {X : Type*} [topological_space X] (A B : set X)
  : Top.of (A ∩ B : set X) ⟶ Top.of B :=
  ⟨set.inclusion (set.inter_subset_right A B), continuous_inclusion (set.inter_subset_right A B)⟩

lemma excision_sq_comm {X : Type*} [topological_space X] (A B : set X)
  : excision_inner_map A B ≫ excision_include A
  = excision_include_inter A B ≫ excision_outer_map A B := by { ext, refl }

def excision_map {X : Type*} [topological_space X] (A B : set X)
  : category_theory.arrow.mk (excision_inner_map A B)
  ⟶ category_theory.arrow.mk (excision_outer_map A B) :=
  category_theory.arrow.hom_mk (excision_sq_comm A B).symm

lemma bounded_by_subcomplex_inclusion_iso_of_contains_univ (R : Type) [comm_ring R]
  {X : Top} (cov : set (set X)) (h : set.univ ∈ cov)
  : category_theory.is_iso (bounded_by_subcomplex_inclusion R cov) :=
begin
  apply homological_complex.is_iso_of_degreewise_is_iso, intro i, 
  dsimp [bounded_by_subcomplex_inclusion, Module.subcomplex_of_compatible_submodules_inclusion],
  refine category_theory.is_iso.of_iso (linear_equiv.to_Module_iso' (linear_equiv.of_bijective
                ((bounded_by_subcomplex_inclusion R cov).f i) _ _)),
  { exact submodule.injective_subtype _ },
  { rw [← set.range_iff_surjective, ← linear_map.range_coe],
    refine eq.trans (congr_arg _ _) submodule.top_coe, convert submodule.range_subtype _,
    symmetry, rw eq_top_iff,
    rw ← subset_subcomplex_univ,
    refine subset_subcomplex_le_bounded_by_subcomplex R _ set.univ _ i,
    exact h }
end.

-- move this to homological algebra
lemma is_pushout_of_is_is_pushout_eval {V : Type*} [category_theory.category V]
  [category_theory.limits.has_zero_morphisms V] {ι : Type*} {c : complex_shape ι}
  {W X Y Z : homological_complex V c} (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
  (H : ∀ n, category_theory.is_pushout (f.f n) (g.f n) (h.f n) (i.f n))
  : category_theory.is_pushout f g h i :=
begin
  refine category_theory.is_pushout.of_is_colimit' _ _,
  { constructor, ext n, dsimp, exact (H n).to_comm_sq.w },
  { apply homological_complex.is_colimit_of_is_colimit_eval, intro n,
    have functors_eq : category_theory.limits.span f g ⋙ homological_complex.eval V c n
                     = category_theory.limits.span (f.f n) (g.f n),
    { refine category_theory.functor.hext _ _,
      { intro ℓ, cases ℓ; try { cases ℓ }; refl },
      { intros ℓ ℓ' a, cases a,
        { cases ℓ; try { cases ℓ }; refl },
        { cases a_1; refl } } },
    convert (H n).is_colimit,
    { simp [category_theory.comm_sq.cocone, category_theory.is_pushout.cocone,
            category_theory.functor.map_cocone, category_theory.limits.cocones.functoriality,
            homological_complex.eval],
      transitivity { category_theory.limits.cocone .
                     X := (category_theory.limits.pushout_cocone.mk (h.f n) (i.f n) (H n).to_comm_sq.w).X,
                     ι := { app := (category_theory.limits.pushout_cocone.mk (h.f n) (i.f n) (H n).to_comm_sq.w).ι.app,
                            naturality' := (category_theory.limits.pushout_cocone.mk (h.f n) (i.f n) (H n).to_comm_sq.w).ι.naturality' } },
      { congr,
        { assumption },
        { assumption },
        { ext, refl,
          intros ℓ ℓ' hℓ, cases hℓ, 
          cases ℓ; try { cases ℓ }; refl },
        { apply proof_irrel_heq } },
      { apply heq_of_eq, congr } } }
end

lemma is_pushout_of_iso_pushout {V : Type*} [category_theory.category V]
  [category_theory.abelian V]
  {X X' A A' B B' Y Y' : V}
  (f : X ⟶ A) (g : X ⟶ B) (h : A ⟶ Y) (i  : B ⟶ Y) 
  (f' : X' ⟶ A') (g' : X' ⟶ B') (h' : A' ⟶ Y') (i' : B' ⟶ Y')
  (ϕ : X ≅ X') (α : A ≅ A') (β : B ≅ B') (ψ : Y ≅ Y')
  (w1 : f ≫ α.hom = ϕ.hom ≫ f') (w2 : g ≫ β.hom = ϕ.hom ≫ g')
  (w3 : h ≫ ψ.hom = α.hom ≫ h') (w4 : i ≫ ψ.hom = β.hom ≫ i')
  (H : category_theory.is_pushout f' g' h' i') : category_theory.is_pushout f g h i :=
begin
  have w : f ≫ h = g ≫ i,
  { rw ← category_theory.iso.eq_comp_inv at w1 w2 w3 w4,
    rw [w1, w2, w3, w4],
    simp, exact H.to_comm_sq.w },
  refine ⟨⟨w⟩, _⟩,
  constructor,
  let span_iso : category_theory.limits.span f g ≅ category_theory.limits.span f' g' 
               := category_theory.limits.span_ext ϕ α β w1.symm w2.symm,
  refine category_theory.limits.is_colimit.of_cocone_equiv
           (category_theory.limits.cocones.precompose_equivalence span_iso).symm _,
  refine category_theory.limits.is_colimit.of_iso_colimit H.is_colimit _,
  refine category_theory.limits.cocones.ext ψ.symm _,
  intro c, cases c,
  { dsimp [category_theory.is_pushout.cocone, category_theory.comm_sq.cocone],
    rw [← category_theory.iso.inv_comp_eq, ← category_theory.category.assoc,
        ← category_theory.iso.eq_comp_inv] at w1 w3,
    rw [category_theory.category.assoc, ← w3, ← category_theory.category.assoc, ← w1],
    rw category_theory.category.assoc, refl },
  cases c,
  { dsimp [category_theory.is_pushout.cocone, category_theory.comm_sq.cocone],
    rw [← category_theory.iso.inv_comp_eq, ← category_theory.category.assoc,
        ← category_theory.iso.eq_comp_inv] at w3,
    exact w3.symm },
  { dsimp [category_theory.is_pushout.cocone, category_theory.comm_sq.cocone],
    rw [← category_theory.iso.inv_comp_eq, ← category_theory.category.assoc,
        ← category_theory.iso.eq_comp_inv] at w4,
    exact w4.symm }
end

lemma Module.sum_is_pushout' (R : Type*) [comm_ring R] {U : Type*}
  [add_comm_group U] [module R U] (A B : submodule R U)
  : category_theory.is_pushout (Module.of_hom (submodule.of_le (@inf_le_left _ _ A B)))
                               (Module.of_hom (submodule.of_le (@inf_le_right _ _ A B)))
                               (Module.of_hom (submodule.of_le (@le_sup_left _ _ A B)))
                               (Module.of_hom (submodule.of_le (@le_sup_right _ _ A B))) :=
begin
  refine ⟨_, _⟩,
  { constructor, ext x, cases x, refl },
  { constructor,
    let f : ∀ c : category_theory.limits.pushout_cocone 
                    (Module.of_hom (submodule.of_le (@inf_le_left _ _ A B)))
                    (Module.of_hom (submodule.of_le (@inf_le_right _ _ A B))),
            A → B → c.X := λ c y z, c.inl y + c.inr z,
    have hf : ∀ c y hy z hz y' hy' z' hz', y + z = y' + z' → f c ⟨y, hy⟩ ⟨z, hz⟩ = f c ⟨y', hy'⟩ ⟨z', hz'⟩,
    { intros c y hy z hz y' hy' z' hz' H,
      dsimp [f],
      rw [← eq_sub_iff_add_eq, add_sub_assoc, add_comm, ← sub_eq_iff_eq_add] at H ⊢,
      have : y - y' ∈ A ⊓ B,
      { refine ⟨submodule.sub_mem _ hy hy', _⟩,
        rw H, exact submodule.sub_mem _ hz' hz },
      rw [← map_sub, ← map_sub],
      change c.inl ⟨y - y', submodule.sub_mem _ hy hy'⟩ = c.inr ⟨z' - z, submodule.sub_mem _ hz' hz⟩,
      simp_rw ← H,
      change c.inl (Module.of_hom (submodule.of_le (@inf_le_left _ _ A B)) ⟨y - y', this⟩)
            = c.inr (Module.of_hom (submodule.of_le (@inf_le_right _ _ A B)) ⟨y - y', this⟩),
      rw [← category_theory.comp_apply, category_theory.limits.pushout_cocone.condition], --← category_theory.comp_apply],
      refl, },
    let g := λ c (x : A ⊔ B), f c ⟨classical.some (submodule.mem_sup.mp x.property),
                                   classical.some (classical.some_spec (submodule.mem_sup.mp x.property))⟩
                                  ⟨classical.some (classical.some_spec (classical.some_spec (submodule.mem_sup.mp x.property))),
                                   classical.some (classical.some_spec (classical.some_spec (classical.some_spec (submodule.mem_sup.mp x.property))))⟩,
    have g_spec : ∀ c (x : A ⊔ B) y hy z hz, x.val = y + z → g c x = f c ⟨y, hy⟩ ⟨z, hz⟩,
    { rintro c ⟨x, hx⟩ y hy z hz H, apply hf,
      refine eq.trans _ H,
      exact classical.some_spec (classical.some_spec (classical.some_spec (classical.some_spec (submodule.mem_sup.mp hx)))) },
    refine category_theory.limits.pushout_cocone.is_colimit_aux _ _ _ _ _,
    { intro c,
      dsimp [category_theory.limits.pushout_cocone.mk],
      refine linear_map.mk (g c) _ _,
      { rintro ⟨x1, h1⟩ ⟨x2, h2⟩, rw submodule.mem_sup at h1 h2,
        obtain ⟨y1, hy1, z1, hz1, H1⟩ := h1,
        obtain ⟨y2, hy2, z2, hz2, H2⟩ := h2,
        refine eq.trans (g_spec c _ (y1 + y2) (submodule.add_mem _ hy1 hy2)
                                    (z1 + z2) (submodule.add_mem _ hz1 hz2) _) _,
        { simp, rw [← H1, ← H2], ac_refl },
        rw [g_spec c ⟨x1, h1⟩ y1 hy1 z1 hz1 H1.symm, g_spec c ⟨x2, h2⟩ y2 hy2 z2 hz2 H2.symm],
        dsimp [f],
        rw [add_assoc, add_left_comm (c.inr ⟨z1, hz1⟩), ← add_assoc,
            ← map_add c.inl, ← map_add c.inr],
        refl, },
      { rintros r ⟨x, hx⟩,
        rw submodule.mem_sup at hx,
        obtain ⟨y, hy, z, hz, H⟩ := hx,
        rw [g_spec c ⟨x, hx⟩ y hy z hz H.symm,
            g_spec c (r • ⟨x, hx⟩) (r • y) (submodule.smul_mem _ r hy)
                                  (r • z) (submodule.smul_mem _ r hz) _],
        { simp [f], rw [ ← map_smul c.inl, ← map_smul c.inr], refl },
        { rw ← smul_add, rw H, refl } } },
    { intro c, ext x, simp, 
      refine eq.trans (g_spec c _ x.val x.property 0 (submodule.zero_mem _) _) _,
      { symmetry, exact add_zero x.val },
      { simp [f], exact map_zero c.inr } },
    { intro c, ext x, simp, 
      refine eq.trans (g_spec c _ 0 (submodule.zero_mem _) x.val x.property _) _,
      { symmetry, exact zero_add x.val },
      { simp [f], exact map_zero c.inl } },
    { intros c m h,
      ext x, cases x with x hx, rw submodule.mem_sup at hx,
      obtain ⟨y, hy, z, hz, H⟩ := hx,
      rw ← ( _ : Module.of_hom (submodule.of_le (@le_sup_left _ _ A B)) ⟨y, hy⟩
               + Module.of_hom (submodule.of_le (@le_sup_right _ _ A B)) ⟨z, hz⟩
               = ⟨x, hx⟩),
      rw [map_add, map_add],
      apply congr_arg2,
      { refine eq.trans _ (g_spec c _ y hy 0 (submodule.zero_mem _) _).symm,
        { transitivity c.inl ⟨y, hy⟩,
          { rw ← category_theory.comp_apply,
            refine congr_fun (congr_arg _ _) _,
            exact h category_theory.limits.walking_span.left },
          { dsimp [f],
            refine eq.trans _ (congr_arg _ (eq.symm (map_zero c.inr))),
            exact (add_zero _).symm } },
        { exact (add_zero _).symm } },
      { refine eq.trans _ (g_spec c _ 0 (submodule.zero_mem _) z hz _).symm,
        { transitivity c.inr ⟨z, hz⟩,
          { rw ← category_theory.comp_apply,
            refine congr_fun (congr_arg _ _) _,
            exact h category_theory.limits.walking_span.right },
          { dsimp [f],
            refine eq.trans _ (congr_arg2 has_add.add (eq.symm (map_zero c.inl)) (refl (c.inr ⟨z, hz⟩))),
            exact (zero_add _).symm } },
        { exact (zero_add _).symm } },
      { exact subtype.eq H } } }
end

lemma eq_to_hom_apply_heq {C : Type*} [category_theory.category C]
  [category_theory.concrete_category C]
  {X Y : C} (h : X = Y) (x : X) : @category_theory.eq_to_hom C _ X Y h x == x :=
begin
  cases h, apply heq_of_eq, simp
end

lemma Module.sum_is_pushout (R : Type*) [comm_ring R]
  {X A B Y : Module R} {f : X ⟶ A} {g : X ⟶ B} {f' : A ⟶ Y} {g' : B ⟶ Y}
  (U : Module R) (i : X ⟶ U) (j : A ⟶ U) (k : B ⟶ U) (ℓ : Y ⟶ U)
  (hi : function.injective i) (hj : function.injective j)
  (hk : function.injective k) (hℓ : function.injective ℓ)
  (hf : f ≫ j = i) (hg : g ≫ k = i) (hf' : f' ≫ ℓ = j) (hg' : g' ≫ ℓ = k)
  (H  : linear_map.range i = linear_map.range j ⊓ linear_map.range k)
  (H' : linear_map.range ℓ = linear_map.range j ⊔ linear_map.range k)
  : category_theory.is_pushout f g f' g' :=
  let i' := (linear_equiv.of_injective i hi).to_Module_iso'_left,
      j' := (linear_equiv.of_injective j hj).to_Module_iso'_left,
      k' := (linear_equiv.of_injective k hk).to_Module_iso'_left,
      ℓ' := (linear_equiv.of_injective ℓ hℓ).to_Module_iso'_left
  in 
  have hij : linear_map.range i ≤ linear_map.range j,
  { rw ← hf, exact le_of_eq_of_le (linear_map.range_comp _ _) linear_map.map_le_range },
  have hik : linear_map.range i ≤ linear_map.range k,
  { rw ← hg, exact le_of_eq_of_le (linear_map.range_comp _ _) linear_map.map_le_range },
  have hjℓ : linear_map.range j ≤ linear_map.range ℓ,
  { rw ← hf', exact le_of_eq_of_le (linear_map.range_comp _ _) linear_map.map_le_range },
  have hkℓ : linear_map.range k ≤ linear_map.range ℓ,
  { rw ← hg', exact le_of_eq_of_le (linear_map.range_comp _ _) linear_map.map_le_range },
  begin
    have := is_pushout_of_iso_pushout (Module.of_hom (submodule.of_le hij))
                                      (Module.of_hom (submodule.of_le hik))
                                      (Module.of_hom (submodule.of_le hjℓ))
                                      (Module.of_hom (submodule.of_le hkℓ))
                                      _ _ _ _
                                      (category_theory.eq_to_iso _)
                                      (category_theory.iso.refl _) (category_theory.iso.refl _)
                                      (category_theory.eq_to_iso _)
                                      _ _ _ _ 
                                      (Module.sum_is_pushout' R (linear_map.range j) (linear_map.range k)),
    swap, { congr; exact H }, swap, { congr; exact H' },
    swap, { ext, dsimp, apply eq_of_heq, congr; try { exact H },
            { ext x, rw [← linear_map.mem_range, ← linear_map.mem_range, ← linear_map.mem_range],
              rw [← submodule.mem_inf, H] },
            { symmetry, apply eq_to_hom_apply_heq } },
    swap, { ext, dsimp, apply eq_of_heq, congr; try { exact H },
            { ext x, rw [← linear_map.mem_range, ← linear_map.mem_range, ← linear_map.mem_range],
              rw [← submodule.mem_inf, H] },
            { symmetry, apply eq_to_hom_apply_heq } },
    swap, { ext, cases x with x hx, dsimp [submodule.of_le], 
            apply eq_of_heq, 
            transitivity ↑(linear_map.cod_restrict (linear_map.range ℓ) (linear_map.range j).subtype (λ c, hjℓ c.property) ⟨x, hx⟩),
            congr; try { ext, rw H', },
            { apply eq_to_hom_apply_heq },
            refl },
    swap, { ext, cases x with x hx, dsimp [submodule.of_le], 
            apply eq_of_heq, 
            transitivity ↑(linear_map.cod_restrict (linear_map.range ℓ) (linear_map.range k).subtype (λ c, hkℓ c.property) ⟨x, hx⟩),
            congr; try { ext, rw H', },
            { apply eq_to_hom_apply_heq },
            refl },
    refine is_pushout_of_iso_pushout _ _ _ _ _ _ _ _ i' j' k' ℓ' _ _ _ _ this,
    { ext x, dsimp [i', j'], rw [← category_theory.comp_apply, hf] },
    { ext x, dsimp [i', k'], rw [← category_theory.comp_apply, hg] },
    { ext x, dsimp [ℓ', j'], rw [← category_theory.comp_apply, hf'] },
    { ext x, dsimp [ℓ', k'], rw [← category_theory.comp_apply, hg'] },
  end

lemma singular_chain_complex_basis_natural (R : Type*) [comm_ring R] {X Y : Top}
  (f : X ⟶ Y) (n : ℕ)
  : ((singular_chain_complex R).map f).f n ∘ (singular_chain_complex_basis R n).get_basis X
  = (singular_chain_complex_basis R n).get_basis Y ∘ (λ p, ⟨(), p.2 ≫ f⟩) :=
begin
  apply funext, rintro ⟨i, σ⟩, cases i,
  dsimp,
  rw [← simplex_to_chain_is_basis, ← simplex_to_chain_is_basis],
  dsimp [simplex_to_chain],
  rw singular_chain_complex_map
end

lemma range_of_singular_chain_complex_include_subspace {X : Type*} [topological_space X]
  (R : Type*) [comm_ring R] (S : set X) (cov : set (set S)) (h : set.univ ∈ cov) (n : ℕ)
  : (linear_map.dom_restrict (((singular_chain_complex R).map (⟨subtype.val, continuous_subtype_val⟩ : Top.of S ⟶ Top.of X)).f n)
                             (@bounded_by_submodule R _ (Top.of S) cov n)).range
  = subset_submodule R X S n :=
begin
  transitivity submodule.map (((singular_chain_complex R).map (⟨subtype.val, continuous_subtype_val⟩ : Top.of S ⟶ Top.of X)).f n)
                             (@bounded_by_submodule R _ (Top.of S) cov n),
  { ext, simp, split,
    { rintros ⟨⟨y, hy⟩, h'⟩, exact ⟨y, hy, h'⟩ },
    { rintros ⟨y, hy, h'⟩, exact ⟨⟨y, hy⟩, h'⟩ } },
  { refine eq.trans (linear_map.map_span _ _) _,
    delta subset_submodule bounded_by_submodule spanned_by_sat,
    rw ← set.image_comp,
    refine congr_arg _ _,
    rw singular_chain_complex_basis_natural,
    rw set.image_comp,
    congr,
    ext, cases x with i σ, cases i,
    simp, split,
    { rintro ⟨i, τ, ⟨s, hs, hτ⟩, h⟩, subst h, 
      refine subset_trans (set.range_comp_subset_range _ _) _,
      exact subset_of_eq subtype.range_val, },
    { intro h',
      let τ : C(topological_simplex n, S)
          := ⟨(λ p, ⟨σ p, h' (set.mem_range_self p)⟩), _⟩,
      { refine ⟨(), τ, ⟨set.univ, h, set.subset_univ _⟩, _⟩, ext, refl },
      { continuity } } }
end

lemma range_of_bounded_by_subcomplex_inclusion {X : Type*} [topological_space X]
  (R : Type*) [comm_ring R] (cov : set (set X)) (n : ℕ)
  : linear_map.range ((@bounded_by_subcomplex_inclusion R _ (Top.of X) cov).f n)
  = bounded_by_submodule R cov n :=
begin
  simp [bounded_by_subcomplex_inclusion, Module.subcomplex_of_compatible_submodules_inclusion],
  refl
end

lemma bounded_by_sup {X : Type*} [topological_space X]
  (R : Type*) [comm_ring R] (cov cov' : set (set X)) (n : ℕ)
  : @bounded_by_submodule R _ (Top.of X) cov n ⊔ bounded_by_submodule R cov' n
  = bounded_by_submodule R (cov ∪ cov') n :=
begin
  delta bounded_by_submodule spanned_by_sat,
  rw submodule.sup_spans R,
  congr,
  simp,
  rw ← set.image_union,
  congr,
  ext x, split; intro h,
  { cases h with h,
    { obtain ⟨s, hs1, hs2⟩ := h, exact ⟨s, or.inl hs1, hs2⟩ },
    { obtain ⟨s, hs1, hs2⟩ := h, exact ⟨s, or.inr hs1, hs2⟩ } },
  { obtain ⟨s, h', h''⟩ := h, cases h' with h',
    { left, exact ⟨s, h', h''⟩ },
    { right, exact ⟨s, h', h''⟩ } }
end

lemma zero_ring_all_iso (R : Type*) [comm_ring R] (h : (1 : R) = 0) {M N : Module R}
  (f : M ⟶ N) : category_theory.is_iso f :=
  ⟨⟨0, by { simp, ext, change 0 = x, transitivity (1 : R) • x, rw h, simp, simp },
      by { simp, ext, change 0 = x, transitivity (1 : R) • x, rw h, simp, simp }⟩⟩.

theorem excision {X : Type*} [topological_space X] (R : Type*) [comm_ring R]
  (A B : set X) (hA : is_open A) (hB : is_open B) (hCov : A ∪ B = ⊤)
  : quasi_iso ((singular_chain_complex_of_pair R).map (excision_map A B)) :=
begin
  by_cases htrivial : (1 : R) = (0 : R),
  { constructor, intro, apply zero_ring_all_iso, exact htrivial },
  have hnontriv : nontrivial R := ⟨⟨1, 0, htrivial⟩⟩,

  letI := singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair_quasi_iso
            R (excision_outer_map A B) _ { A, B } _ _,
  { have hA : category_theory.is_iso (@bounded_by_subcomplex_inclusion R _ (Top.of A) {set.univ}),
    { apply bounded_by_subcomplex_inclusion_iso_of_contains_univ, apply set.mem_singleton },
    have hInter : category_theory.is_iso (@bounded_by_subcomplex_inclusion R _ (Top.of (A ∩ B : set X))
                                            (pullback_family_of_sets {set.univ} (excision_inner_map A B))),
    { apply bounded_by_subcomplex_inclusion_iso_of_contains_univ, existsi set.univ, simp },
    let f1 := singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair R 
               (category_theory.arrow.mk (excision_inner_map A B)) {set.univ},
    have h1 : category_theory.is_iso f1,
    { apply_with category_theory.functor.map_is_iso {instances := ff}, 
      apply_with category_theory.arrow.is_iso_of_iso_left_of_is_iso_right {instances := ff},
      exact hInter, exact hA },
    letI := h1,
    have H : ∀ s, s ∈ {set.univ} → (∃ t, t ∈ {A, B} ∧ excision_include A '' s ⊆ t),
    { intros s hs, existsi A, split, { apply set.mem_insert }, { simp [excision_include] } },
    let f2 := singular_chain_complex_of_pair_under_cover_map R (excision_map A B) {set.univ} {A, B} H,
    let f3 := (singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair R (excision_outer_map A B) {A, B}),
    suffices : category_theory.is_iso f2
             ∧ category_theory.inv f1 ≫ f2 ≫ f3
             = (singular_chain_complex_of_pair R).map (excision_map A B),
    { rw ← this.right, letI := this.left, apply_instance, },
    split,    
    { let i : Π n, (bounded_by_subcomplex R (pullback_family_of_sets {set.univ} (excision_inner_map A B))).X n
                 ⟶ ((singular_chain_complex R).obj (Top.of X)).X n
            := λ n, linear_map.dom_restrict (((singular_chain_complex R).map (⟨subtype.val, continuous_subtype_val⟩ : Top.of (A ∩ B : set X) ⟶ Top.of X)).f n) _,
      let j : Π n, (bounded_by_subcomplex R {set.univ}).X n
                 ⟶ ((singular_chain_complex R).obj (Top.of X)).X n
            := λ n, linear_map.dom_restrict (((singular_chain_complex R).map (⟨subtype.val, continuous_subtype_val⟩ : Top.of A ⟶ Top.of X)).f n) _,
      let k : Π n, (bounded_by_subcomplex R (pullback_family_of_sets {A, B} (excision_outer_map A B))).X n
                 ⟶ ((singular_chain_complex R).obj (Top.of X)).X n
            := λ n, linear_map.dom_restrict (((singular_chain_complex R).map (⟨subtype.val, continuous_subtype_val⟩ : Top.of B ⟶ Top.of X)).f n) _,
      let ℓ : Π n, (bounded_by_subcomplex R {A, B}).X n
                 ⟶ ((singular_chain_complex R).obj (Top.of X)).X n
            := λ n, (bounded_by_subcomplex_inclusion R {A, B}).f n,
      dsimp [f2, singular_chain_complex_of_pair_under_cover_map],
      apply coker_of_cocartesian_square_is_iso,
      apply is_pushout_of_is_is_pushout_eval, intro n,
      refine Module.sum_is_pushout R (((singular_chain_complex R).obj (Top.of X)).X n)
                                    (i n) (j n) (k n) (ℓ n) _ _ _ _ _ _ _ _ _ _,
      { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, apply subtype.eq,
        exact singular_chain_complex_map_inj R (⟨subtype.val, continuous_subtype_val⟩ : Top.of (A ∩ B : set X) ⟶ Top.of X) subtype.val_injective n hxy },
      { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, apply subtype.eq,
        exact singular_chain_complex_map_inj R (⟨subtype.val, continuous_subtype_val⟩ : Top.of A ⟶ Top.of X) subtype.val_injective n hxy, },
      { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, apply subtype.eq,
        exact singular_chain_complex_map_inj R (⟨subtype.val, continuous_subtype_val⟩ : Top.of B ⟶ Top.of X) subtype.val_injective n hxy },
      { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, apply subtype.eq, exact hxy },
      { apply linear_map.ext, rintro ⟨x, hx⟩,
        rw category_theory.comp_apply,
        dsimp [i, j],
        dsimp [bounded_by_pullback_chain_inclusion, bounded_by_subcomplex_map,
               subcomplex_spanned_by_map],
        rw [← category_theory.comp_apply, ← homological_complex.comp_f,
            ← (singular_chain_complex R).map_comp],
        congr, },
      { apply linear_map.ext, rintro ⟨x, hx⟩,
        rw category_theory.comp_apply,
        dsimp [i, k],
        delta bounded_by_subcomplex_map subcomplex_spanned_by_map,
        rw [linear_map.cod_restrict_apply, linear_map.dom_restrict_apply,
            ← category_theory.comp_apply, ← homological_complex.comp_f,
            ← (singular_chain_complex R).map_comp],
        congr },
      { apply linear_map.ext, rintro ⟨x, hx⟩,
        rw category_theory.comp_apply,
        dsimp [ℓ, j],
        rw [← category_theory.comp_apply, ← homological_complex.comp_f],
        rw ← cover_inclusion_natural,
        rw [homological_complex.comp_f, category_theory.comp_apply],
        congr, },
      { apply linear_map.ext, rintro ⟨x, hx⟩,
        rw category_theory.comp_apply,
        dsimp [ℓ, k],
        rw [← category_theory.comp_apply, ← homological_complex.comp_f],
        delta bounded_by_pullback_chain_inclusion,
        rw ← cover_inclusion_natural,
        rw [homological_complex.comp_f, category_theory.comp_apply],
        congr, },
      { dsimp [i, j, k],
        refine eq.trans (range_of_singular_chain_complex_include_subspace R _ _ _ n) _,
        { exact ⟨set.univ, set.mem_singleton _, set.preimage_univ⟩, },
        refine eq.trans _ (congr_arg2 _ (range_of_singular_chain_complex_include_subspace R _ _ _ n).symm
                                        (range_of_singular_chain_complex_include_subspace R _ _ _ n).symm),
        delta subset_submodule bounded_by_submodule spanned_by_sat,
        rw submodule.inf_spans_free R ((singular_chain_complex_basis R n).get_basis (Top.of X))
                                      _ _ (set.image_subset_range _ _) (set.image_subset_range _ _),
        rw [set.image_inter (@basis.injective _ R _ _ _ _
                                        ((singular_chain_complex_basis R n).get_basis (Top.of X))
                                        hnontriv)],
        congr,
        simp, ext x, split; intro h,
        { exact ⟨subset_trans h (set.inter_subset_left A B),
                 subset_trans h (set.inter_subset_right A B)⟩ },
        { exact set.subset_inter h.left h.right },
        { exact eq.refl set.univ },
        { refine ⟨B, _, _⟩,
          { rw set.pair_comm, apply set.mem_insert },
          { apply set.eq_univ_of_univ_subset, 
            rw ← set.image_subset_iff,
            rw set.image_univ,
            exact subset_of_eq subtype.range_val, } } },
      { dsimp [ℓ, j, k],
        refine eq.trans (range_of_bounded_by_subcomplex_inclusion R _ n) _,
        refine eq.trans _ (congr_arg2 _ (range_of_singular_chain_complex_include_subspace R _ _ _ n).symm
                                        (range_of_singular_chain_complex_include_subspace R _ _ _ n).symm),
        delta subset_submodule,
        rw bounded_by_sup,
        congr,
        { exact eq.refl set.univ },
        { refine ⟨B, _, _⟩,
          { rw set.pair_comm, apply set.mem_insert },
          { apply set.eq_univ_of_univ_subset, 
            rw ← set.image_subset_iff,
            rw set.image_univ,
            exact subset_of_eq subtype.range_val, } } }, },
    { rw category_theory.is_iso.inv_comp_eq,
      dsimp [f2, f3, f1],
      apply singular_chain_complex_of_pair_under_cover_to_singular_chain_complex_of_pair_naturality } },
  { rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, ext, exact hxy },
  { simp, exact ⟨hA, hB⟩ },
  { simp, exact hCov }
end.

