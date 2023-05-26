import linear_algebra.finsupp_vector_space
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import algebra.big_operators.finsupp
import .category_theory

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
    (R : Type*) [semiring R] (X : Type*)
    : linear_independent R (λ x : X, finsupp.single x (1 : R)) :=
finsupp.basis_single_one.linear_independent

lemma free_module_basis_spanning
    (R : Type*) [semiring R] (X : Type*)
    : submodule.span R (set.range (λ x : X, finsupp.single x (1 : R))) = ⊤ :=
by rw [← finsupp.supported_univ, finsupp.supported_eq_span_single, set.image_univ]

local attribute [instance] classical.prop_decidable
universes u v w

lemma basis.span_image {R : Type u} [semiring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) (S : set ι) :
  submodule.span R (b '' S) = (finsupp.supported R R S).comap (b.repr : M →ₗ[R] ι →₀ R) :=
by rw [← b.repr.symm_symm, ← b.repr.symm.map_eq_comap, finsupp.supported_eq_span_single,
       submodule.map_span, set.image_image]; refl

lemma basis.mem_span_image_iff {R : Type u} [semiring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set ι} {x : M} :
  x ∈ submodule.span R (b '' S) ↔ (∀ i, b.repr x i ≠ 0 → i ∈ S) :=
by simp only [b.span_image, set.subset_def, finsupp.mem_supported, finset.mem_coe,
              submodule.mem_comap, linear_equiv.coe_coe, finsupp.mem_support_iff]

lemma basis.span_of_subset_range {R : Type u} [semiring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set M} (hS : S ⊆ set.range b) :
  submodule.span R S = (finsupp.supported R R (b ⁻¹' S)).comap (b.repr : M →ₗ[R] ι →₀ R) :=
by rw [← b.span_image, set.image_preimage_eq_of_subset hS]

lemma basis.mem_span_iff {R : Type u} [semiring R] {M : Type v}
  [add_comm_monoid M] [module R M] {ι : Type w}
  (b : basis ι R M) {S : set M} (hS : S ⊆ set.range b) (x : M) :
  x ∈ submodule.span R S ↔ (∀ i, b.repr x i ≠ 0 → b i ∈ S) :=
show x ∈ submodule.span R S ↔ (∀ i, b.repr x i ≠ 0 → i ∈ b ⁻¹' S),
by rw [← b.mem_span_image_iff, set.image_preimage_eq_of_subset hS]

lemma submodule.inf_spans_free {R : Type*} [semiring R] {M : Type*}
  [add_comm_monoid M] [module R M] {ι : Type*}
  (b : basis ι R M)
  {S T : set M} (hS : S ⊆ set.range b) (hT : T ⊆ set.range b) :
  submodule.span R S ⊓ submodule.span R T = submodule.span R (S ∩ T) :=
have hST : S ∩ T ⊆ set.range b := (set.inter_subset_left _ _).trans hS,
by simp only [b.span_of_subset_range, *, ← submodule.comap_inf, set.preimage_inter,
              finsupp.supported_inter]

noncomputable
def basis.quotient (ι : Type*) (R : Type*) (M : Type*) [ring R] [add_comm_group M]
  [module R M] (N : submodule R M) (b : basis ι R M) (s : setoid ι)
  (H : N = submodule.span R (set.image (λ p : ι × ι, b p.fst - b p.snd) { p | p.fst ≈ p.snd }))
  : basis (quotient s) R (M ⧸ N) := 
  ⟨linear_equiv.of_linear 
    (N.liftq (b.constr ℕ (λ i, finsupp.single (quotient.mk i) (1 : R))) $ by {
      rw [H, linear_map.le_ker_iff_map, eq_bot_iff, submodule.map_span_le], 
      rintros x ⟨⟨i, j⟩, hij, h⟩, subst h,
      simp only [map_sub, basis.constr_basis, submodule.mem_bot],
      apply sub_eq_zero_of_eq,
      congr' 1,
      exact quotient.sound hij
    })
    (finsupp.lift (M ⧸ N) R _ $ quotient.lift (λ i, N.mkq (b i)) $ by {
      intros i j hij, 
      dsimp only [],
      rw [← sub_eq_zero, ← map_sub, H,
          submodule.mkq_apply, submodule.quotient.mk_eq_zero],
      apply submodule.subset_span,
      exact ⟨(i, j), hij, rfl⟩
    })
    (by {
      apply finsupp.lhom_ext', rintros ⟨i⟩,
      apply linear_map.ext_ring,
      apply finsupp.ext, rintros ⟨j⟩,
      simp only [basis.constr_basis, submodule.mkq_apply, linear_map.coe_comp,
                 function.comp_app, finsupp.lsingle_apply, finsupp.lift_apply,
                 finsupp.sum_single_index, zero_smul, one_smul,
                 submodule.liftq_apply, linear_map.id_comp],
      refl
    })
    (by {
      apply submodule.linear_map_qext, apply b.ext, intro,
      simp only [submodule.mkq_apply, basis.constr_basis, linear_map.coe_comp,
                 function.comp_app, submodule.liftq_apply, finsupp.lift_apply,
                 finsupp.sum_single_index, quotient.lift_mk, zero_smul, 
                 one_smul, linear_map.id_comp]
    })⟩

lemma basis_constr_of_lin_indep_family_injective {ι : Type*} {R : Type*} {M : Type*} {M' : Type*}
  [ring R] [nontrivial R] [add_comm_group M] [module R M] [add_comm_group M'] [module R M']
  (b : basis ι R M) (f : ι → M') (hf : linear_independent R f)
  : function.injective (basis.constr b ℕ f) :=
begin
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  intros m hm,
  simp only [basis.constr, linear_equiv.coe_mk, linear_map.coe_comp,
             linear_equiv.coe_coe, function.comp_app, finsupp.lmap_domain_apply,
             finsupp.total_map_domain, function.comp.left_id] at hm,
  rw linear_independent_iff at hf,
  specialize hf _ hm,
  rw linear_equiv.map_eq_zero_iff at hf, exact hf
end
