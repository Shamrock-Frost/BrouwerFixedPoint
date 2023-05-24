import linear_algebra.finsupp_vector_space
import algebra.category.Module.abelian
import algebra.category.Module.images
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import algebra.big_operators.finsupp

@[simp]
lemma finsupp.supported_equiv_finsupp_symm_apply_coe {α M R : Type*} [semiring R] [add_comm_monoid M]
  [module R M] (s : set α) (f : s →₀ M):
  (((finsupp.supported_equiv_finsupp s).symm f : finsupp.supported M R s) : α →₀ M) =
    f.map_domain (coe : s → α) := rfl

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
finsupp.basis_single_one.linear_independent

lemma free_module_basis_spanning
    (R : Type*) [semiring R] (X : Type*)
    : submodule.span R (set.range (λ x : X, finsupp.single x (1 : R))) = ⊤ :=
by rw [← finsupp.supported_univ, finsupp.supported_eq_span_single, set.image_univ]

local attribute [instance] classical.prop_decidable
universes u v w

lemma basis.span_image {R : Type u} [comm_ring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) (S : set ι) :
  submodule.span R (b '' S) = (finsupp.supported R R S).comap (b.repr : M →ₗ[R] ι →₀ R) :=
by rw [← b.repr.symm_symm, ← b.repr.symm.map_eq_comap, finsupp.supported_eq_span_single,
  submodule.map_span, set.image_image]; refl

lemma basis.mem_span_image_iff {R : Type u} [comm_ring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set ι} {x : M} :
  x ∈ submodule.span R (b '' S) ↔ (∀ i, b.repr x i ≠ 0 → i ∈ S) :=
by simp [b.span_image, set.subset_def, finsupp.mem_supported]

lemma basis.span_of_subset_range {R : Type u} [comm_ring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set M} (hS : S ⊆ set.range b) :
  submodule.span R S = (finsupp.supported R R (b ⁻¹' S)).comap (b.repr : M →ₗ[R] ι →₀ R) :=
by rw [← b.span_image, set.image_preimage_eq_of_subset hS]

lemma basis.mem_span_iff {R : Type u} [comm_ring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set M} (hS : S ⊆ set.range b) (x : M) :
  x ∈ submodule.span R S ↔ (∀ i, b.repr x i ≠ 0 → b i ∈ S) :=
show x ∈ submodule.span R S ↔ (∀ i, b.repr x i ≠ 0 → i ∈ b ⁻¹' S),
by rw [← b.mem_span_image_iff, set.image_preimage_eq_of_subset hS]

lemma submodule.inf_spans_free {R : Type u} [comm_ring R] {M : Type*}
  [add_comm_monoid M] [module R M] {ι : Type*}
  (b : basis ι R M)
  {S T : set M} (hS : S ⊆ set.range b) (hT : T ⊆ set.range b) :
  submodule.span R S ⊓ submodule.span R T = submodule.span R (S ∩ T) :=
have hST : S ∩ T ⊆ set.range b := (set.inter_subset_left _ _).trans hS,
by simp only [b.span_of_subset_range, *, ← submodule.comap_inf, set.preimage_inter,
  finsupp.supported_inter]

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
           { intros, rw ite_eq_left_iff.mpr _, swap, { intros, contradiction },
             simp [v],
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
  [comm_ring R] [nontrivial R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
  (b : basis ι R M) (f : ι → M') (hf : linear_independent R f)
  : function.injective (basis.constr b R f) :=
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
