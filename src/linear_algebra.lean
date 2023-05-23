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

lemma basis.mem_span_iff (R : Type u) [ring R] {M : Type v}
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

lemma submodule.inf_spans_free (R : Type) [ring R] {M : Type*}
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

lemma submodule.sup_spans (R : Type) [ring R] {M : Type*}
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
end.

/-
It might be better to prove this by looking at stuff as coequalizers and using left adjointness of
the free module functor. 
-/

noncomputable
def basis.quotient_basis (ι : Type*) (R : Type*) (M : Type*) [ring R] [add_comm_group M]
  [module R M] (N : submodule R M) (b : basis ι R M) (s : setoid ι)
  (H : N = submodule.span R (set.image (λ p : ι × ι, b p.fst - b p.snd) { p | p.fst ≈ p.snd }))
  : basis (quotient s) R (M ⧸ N) :=
  let v : quotient s → M ⧸ N := quotient.lift (λ i, submodule.quotient.mk (b i)) 
                                              (by { intros i j hij,
                                                    refine (submodule.quotient.eq N).mpr _,
                                                    rw H,
                                                    refine submodule.subset_span _,
                                                    refine @set.mem_image_of_mem _ _ _ (i, j) _ _,
                                                    exact hij }) in 
  have h1 : linear_independent R v,
  by { have hcoeffs' := b.linear_independent,
       rw linear_independent_iff at ⊢ hcoeffs',
       intros coeffs h,
       let support' := coeffs.support.image quotient.out,
       let coeffs' : ι →₀ R := ⟨support', (λ x, if x ∈ support' then coeffs (quotient.mk x) else 0), _⟩,
       swap, { intro, simp, simp_rw ← and_assoc, simp, intros x hx ha, subst ha, simp, exact hx },
       specialize hcoeffs' coeffs' _,
       { have h' : N.mkq (finsupp.total ι M R b coeffs')
                 = finsupp.total (quotient s) (M ⧸ N) R v coeffs,
         { dsimp [finsupp.total, finsupp.sum],
           rw ← submodule.mkq_apply N,
           rw map_sum,
           apply finset.sum_bij' (λ i _, quot.mk s.r i) _ _ (λ j _, quot.out j),
           { intros, simp, 
             simp [support'] at ha,
             obtain ⟨b, _, hb⟩ := ha, subst hb,
             exact congr_arg quot.out b.out_eq },
           { intros, simp },
           { intros, simp [support'], simp at ha,
             refine ⟨a, ha, rfl⟩ },
           { intros, simp [support'] at ha,
             obtain ⟨b, hb, hb'⟩ := ha, subst hb',
             simp, convert hb,
             exact b.out_eq },
           { intros, 
             rw ite_eq_left_iff.mpr _,
             swap,
             { intros, contradiction },
             simp only [v, submodule.mkq_apply, submodule.quotient.mk_smul],
             refl } }, 
         rw h at h',
         simp at h',
         have H' : N = submodule.span R ((λ i : ι, b (quot.mk s.r i).out - b i) '' { i | (quot.mk s.r i).out ≠ i }),
         { refine eq.trans H _,
           apply le_antisymm,
           { rw submodule.span_le,
             rw set.image_subset_iff,
             rintros ⟨i, j⟩ hij,
             simp,
             rw (_ : b i - b j = (b (quot.mk setoid.r j).out - b j) - (b (quot.mk setoid.r i).out - b i)),
             { refine submodule.sub_mem _ _ _,
               { by_cases hj : (quot.mk s.r j).out = j,
                 { rw hj, rw sub_self, exact submodule.zero_mem _ },
                 { refine submodule.subset_span _, exact set.mem_image_of_mem _ hj } },
               { by_cases hi : (quot.mk s.r i).out = i,
                 { rw hi, rw sub_self, exact submodule.zero_mem _ },
                 { refine submodule.subset_span _, exact set.mem_image_of_mem _ hi } } },
             { have hij' : quot.mk setoid.r i = quot.mk setoid.r j := quotient.sound hij,
               rw hij',
               simp } },
           { rw submodule.span_le,
             rw set.image_subset_iff,
             intros i hi,
             refine submodule.subset_span _,
             simp,
             refine ⟨(quot.mk setoid.r i).out, i, _, rfl⟩,
             exact quotient.mk_out i } },
         rw H' at h',
         rw finsupp.mem_span_image_iff_total at h',
         obtain ⟨l, Hl_supp, Hl⟩ := h',
         dsimp [finsupp.supported] at Hl_supp,
         rw (_ : finsupp.total ι M R (λ (i : ι), b (quot.mk setoid.r i).out - b i) l
               = finsupp.total ι M R (λ (i : ι), b (quot.mk setoid.r i).out) l
               - finsupp.total ι M R b l)
            at Hl,
         { rw sub_eq_iff_eq_add at Hl,
           rw ← map_add at Hl,
           suffices Hl' : l = 0,
           { rw Hl' at Hl,
             simp at Hl,
             exact Hl.symm },
           rw (_ : (finsupp.total ι M R (λ (i : ι), b (quot.mk setoid.r i).out)) l
                 = (finsupp.total ι M R b) (l.map_domain (λ i, (quot.mk setoid.r i).out))) at Hl,
           { rw ← sub_eq_zero at Hl,
             rw ← map_sub at Hl,
             have := linear_independent_iff.mp b.linear_independent _ Hl,
             rw ← finsupp.support_eq_empty,
             rw ← finset.subset_empty,
             intros i hi, change false,
             specialize Hl_supp hi,
             have hi' : (finsupp.map_domain (λ (i : ι), (quot.mk setoid.r i).out) l - (coeffs' + l)) i = 0,
             { rw this, refl },
             simp at hi',
            --  replace this := congr_fun (congr_arg finsupp.to_fun this) i,
             rw [← sub_sub, sub_eq_zero] at hi',
             simp at hi, apply hi,
             rw ← hi',
             convert zero_sub_zero,
             { apply finsupp.map_domain_notin_range,
               rintro ⟨j, hj⟩,
               dsimp at hj, subst hj,
               refine Hl_supp _,
               exact congr_arg quot.out (quot.out_eq _) },
             { rw ite_eq_right_iff,
               rintro ⟨j, _, hj⟩, subst hj,
               exfalso, 
               refine Hl_supp _,
               exact congr_arg quot.out (quot.out_eq _) } },
           { simp [finsupp.total, finsupp.map_domain],
             rw finsupp.sum_sum_index,
             { congr, ext,
               rw [finsupp.sum_single_index],
               apply zero_smul },
             { intro, apply zero_smul },
             { intros, apply add_smul } } },
         { rw [finsupp.total_apply, finsupp.total_apply, finsupp.total_apply],
           simp [finsupp.sum],
           simp_rw [smul_sub],
           simp } },
       ext i,
       have : coeffs' i.out = 0,
       { rw hcoeffs', refl },
       simp [coeffs'] at this,
       exact this },
  have h2 : submodule.span R (set.range v) = ⊤,
  by { rw eq_top_iff,
       intros x hx,
       induction x,
       { have := b.mem_span x,
         simp [submodule.span] at this ⊢,
         intros p Hp,
         refine this (submodule.comap N.mkq p) _,
         rintros t ⟨i, hi⟩, subst hi,
         refine Hp _,
         existsi ⟦i⟧,
         refl },
       { refl } },
  basis.mk h1 h2.

lemma basis_constr_of_lin_indep_family_injective {ι : Type*} {R : Type*} {M : Type*} {M' : Type*}
  [ring R] [nontrivial R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
  (b : basis ι R M) (f : ι → M') (hf : linear_independent R f)
  : function.injective (basis.constr b ℤ f) :=
begin
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  intros m hm,
  simp [basis.constr] at hm,
  rw finsupp.total_map_domain at hm, swap, { exact hf.injective },
  rw function.comp.left_id at hm,
  rw linear_independent_iff at hf,
  specialize hf _ hm,
  rw linear_equiv.map_eq_zero_iff at hf, exact hf
end