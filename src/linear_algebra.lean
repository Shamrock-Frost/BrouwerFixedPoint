import linear_algebra.linear_independent
import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import algebra.big_operators.finsupp

lemma submodule_restrict_app {R : Type*}
  {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}
  [semiring R] [add_comm_monoid M₁] [add_comm_monoid M₂] [add_comm_monoid M₃]
  [module R M₁] [module R M₂] [module R M₃]
  (p : submodule R M₂) (q : submodule R M₃)
  (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
  (hf : ∀ (x : M₁), f x ∈ p)
  (hg : ∀ (y : p), g.dom_restrict p y ∈ q)
  (x : M₁)
  : linear_map.cod_restrict q (linear_map.dom_restrict g p) 
      hg
      (linear_map.cod_restrict p f hf x)
  = linear_map.cod_restrict q (g.comp f) (λ x, hg ⟨f x, hf x⟩) x :=
begin
  ext, refl
end

lemma free_module_basis_linear_independent
    (R : Type*) [ring R] (X : Type*)
    : linear_independent R (λ x : X, finsupp.single x (1 : R)) :=
begin
  rw linear_independent_iff,
  intros y h,
  have h' : y.support.sum (λ a, finsupp.single a (y a)) = 0,
  { rw [← h, finsupp.total_apply], dsimp [finsupp.sum],
    congr, ext, simp },
  ext x,
  have h'' : y.support.sum (λ a, finsupp.single a (y a)) x = 0,
  { rw h', simp },
  rw [finset.sum_apply', finset.sum_eq_single x,
      finsupp.single_eq_same] at h'',
  exact h'',
  { intros, rw finsupp.single_apply_eq_zero,
    intro H, symmetry' at H, contradiction },
  { intro H, rw finsupp.not_mem_support_iff at H, rw H, simp }
end

lemma free_module_basis_spanning
    (R : Type*) [ring R] (X : Type*)
    : submodule.span R (set.range (λ x : X, finsupp.single x (1 : R))) = ⊤ :=
begin
  ext f, rw submodule.mem_span, simp,
  intros p hp,
  -- Should extract this as a common lemma
  have : f = (f.support).sum (λ x, finsupp.single x (f x)),
  { ext x, symmetry, rw [finset.sum_apply', finset.sum_eq_single x, finsupp.single_eq_same],
    { intros b hb h, rw finsupp.single_apply_eq_zero, intro, symmetry' at h, contradiction },
    { intro H, rw finsupp.not_mem_support_iff at H, rw H, simp } },
  rw this,
  apply submodule.sum_mem,
  intros x hx,
  rw ← mul_one (f x),
  generalize h : finsupp.single x (f x * 1) = c,
  have := eq.trans (finsupp.smul_single (f x) x 1) h,
  rw ← this,
  apply submodule.smul_mem,
  apply hp,
  existsi x, refl
end

local attribute [instance] classical.prop_decidable
universes u v w

lemma basis.mem_span_iff (R : Type u) [comm_ring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) (S : set M) (hS : S ⊆ set.range b) (x : M)
  : x ∈ submodule.span R S ↔ (∀ i, b.repr x i ≠ 0 → b i ∈ S) :=
begin
  by_cases ax1 : nonempty ι, swap,
  { simp at ax1,
    have h1 : ∀ y, b.repr y = 0,
    { intro, rw ← finsupp.support_eq_empty, exact @finset.eq_empty_of_is_empty _ ax1 _ },
    have : ∀ y : M, y = 0,
    { intro y, refine eq.trans (b.total_repr y).symm _, rw h1, apply map_zero },
    rw [this x, h1],
    simp, },
  by_cases ax2 : nontrivial R, swap,
  { rw nontrivial_iff at ax2, simp_rw [not_exists, not_not] at ax2,
    have : x = 0 := eq.trans (one_smul R x).symm (eq.trans (congr_arg2 _ (ax2 1 0) (refl x)) (zero_smul _ _)),
    rw this, rw (_ : ∀ y, b.repr y = 0), simp,
    intro, ext, apply ax2 },
  split,
  { intros h i,
    apply submodule.span_induction h,
    { intros y hy1 hy2,
      have := @function.inv_fun_eq _ _ ax1 _ _ (hS hy1),
      dsimp at this,
      rw ← this at hy2, simp at hy2,
      rw finsupp.single_apply at hy2,
      split_ifs at hy2,
      { rw h_1 at this, rw this, exact hy1 },
      { exfalso, apply hy2, refl } },
    { intro hi, exfalso, apply hi, simp },
    { intros y z hy hz hsum,
      simp at hsum,
      by_cases b.repr y i = 0 ∧ b.repr z i = 0,
      { exfalso, rw [h.left, h.right] at hsum, simp at hsum, exact hsum },
      { rw decidable.not_and_iff_or_not at h, cases h with h,
        { exact hy h },
        { exact hz h_1 }, } },
    { intros r x hx hrx, apply hx,
      simp at hrx,
      intro h', rw h' at hrx, apply hrx, simp, } },
  { intro h,
    refine (finsupp.mem_span_iff_total R S x).mpr _,
    let l : S →₀ R := finsupp.comap_domain (@function.inv_fun ι M ax1 (b : ι → M) ∘ subtype.val)
                                           (b.repr x)
                                           _,
    swap,
    { rintros ⟨a, ha⟩ _ ⟨a', ha'⟩ _ haa', simp at ⊢ haa', 
      exact eq.trans (@function.inv_fun_eq _ _ ax1 _ _ (hS ha)).symm
                     (eq.trans (congr_arg b haa') (@function.inv_fun_eq _ _ ax1 _ _ (hS ha'))) },
    existsi l,
    refine eq.trans _ (b.total_repr x),
    simp [finsupp.total, finsupp.sum], 
    refine finset.sum_bij (λ s _, @function.inv_fun ι M ax1 (b : ι → M) s.val)
                          _ _ _ _,
    { intro, simp },
    { rintros ⟨s, hs⟩ hs', simp at ⊢ hs',
      symmetry, exact congr_arg2 _ rfl (@function.inv_fun_eq _ _ ax1 _ _ (hS hs)), },
    { rintros ⟨a, ha⟩ ⟨a', ha'⟩ _ _ haa', apply subtype.eq,
      exact eq.trans (@function.inv_fun_eq _ _ ax1 _ _ (hS ha)).symm
                     (eq.trans (congr_arg b haa') (@function.inv_fun_eq _ _ ax1 _ _ (hS ha'))) },
    { intros i hi, simp at hi,
      refine exists.intro ⟨b i, h i hi⟩ _,
      have : @function.inv_fun _ _ ax1 b (b i) = i,
      { refine (@basis.injective _ _ _ _ _ _ b ax2) _ _ _,
        exact (@function.inv_fun_eq _ _ ax1 _ _ (hS (h i hi))) },
      refine exists.intro _ _,
      { simp, convert hi },
      { symmetry, apply this } } }
end

lemma submodule.inf_spans_free (R : Type) [comm_ring R] {M : Type*}
  [add_comm_monoid M] [module R M] {ι : Type*}
  (b : basis ι R M)
  (S T : set M) (hS : S ⊆ set.range b) (hT : T ⊆ set.range b)
  : submodule.span R S ⊓ submodule.span R T = submodule.span R (S ∩ T) :=
begin
  ext x, split; intro h,
  { simp at h, 
    rw [basis.mem_span_iff R b S hS, basis.mem_span_iff R b T hT] at h, cases h with h1 h2,
    rw basis.mem_span_iff R b (S ∩ T) (subset_trans (set.inter_subset_left S T) hS),
    intros i hi, exact ⟨h1 i hi, h2 i hi⟩ },
  { rw basis.mem_span_iff R b (S ∩ T) (subset_trans (set.inter_subset_left S T) hS) at h,
    simp, rw [basis.mem_span_iff R b S hS, basis.mem_span_iff R b T hT],
    split; intros i hi, { exact (h i hi).left }, { exact (h i hi).right } }
end

lemma submodule.sup_spans (R : Type) [comm_ring R] {M : Type*}
  [add_comm_monoid M] [module R M] (S T : set M)
  : submodule.span R S ⊔ submodule.span R T = submodule.span R (S ∪ T) :=
begin
  apply eq_of_forall_ge_iff, intro N,
  rw sup_le_iff,
  split; intro h,
  { rw submodule.span_le,
    intros x hx, cases hx,
    { exact h.left (submodule.subset_span hx) },
    { exact h.right (submodule.subset_span hx) } },
  { split; refine le_trans _ h; apply submodule.span_mono; simp }
end

lemma map_domain_inj_of_inj {α β : Type*} {M : Type*} [add_comm_monoid M]
  (f : α → β) (hf : function.injective f)
  : function.injective (@finsupp.map_domain α β M _ f) :=
begin
  intros p q h, ext a,
  convert congr_arg (λ g : β →₀ M, g (f a)) h;
  rw finsupp.map_domain_apply hf, 
end