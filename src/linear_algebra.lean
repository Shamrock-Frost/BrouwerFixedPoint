import linear_algebra.finsupp_vector_space
import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
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
by simp [b.span_image, set.subset_def, finsupp.mem_supported].

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

/-
Proof idea: `quotient s` is a coequalizer of the congruence `s.rel`,
and the left adjoint Module.free preserves this colimit.
-/
open category_theory category_theory.limits

noncomputable
def basis.quotient (ι : Type*) (R : Type*) (M : Type*) [ring R] [add_comm_group M]
  [module R M] (N : submodule R M) (b : basis ι R M) (s : setoid ι)
  (H : N = submodule.span R (set.image (λ p : ι × ι, b p.fst - b p.snd) { p | p.fst ≈ p.snd }))
  : basis (quotient s) R (M ⧸ N) :=
  let p1 : subtype s.rel.uncurry ⟶ ι := _root_.prod.fst ∘ subtype.val,
      p2 : subtype s.rel.uncurry ⟶ ι := _root_.prod.snd ∘ subtype.val,
      c1 : cofork ((Module.free R).map p1) ((Module.free R).map p2)
         := (cocones.precompose (parallel_pair_comp _ _ _).inv).obj
              ((Module.free R).map_cocone (types.quotient_cocone s)),
      h1 : is_colimit c1 :=
        (is_colimit.precompose_inv_equiv (parallel_pair_comp _ _ _) _).inv_fun
        $ @is_colimit_of_preserves _ _ _ _ _ _ _ _ _
            (types.quotient_cocone_is_colimit _)
            (Module.adj R).left_adjoint_preserves_colimits.preserves_colimits_of_shape.preserves_colimit,
      h2 := preadditive.is_colimit_cokernel_cofork_of_cofork h1,
      i1 := h2.cocone_point_unique_up_to_iso (Module.cokernel_is_colimit _),
      i2 : (M ⧸ N) ≃ₗ[R] ((ι →₀ R) ⧸ linear_map.range ((Module.free R).map p1 - (Module.free R).map p2))
         := submodule.quotient.equiv N _ b.repr
            $ by { rw H, simp only [Module.free_map],
                   refine eq.trans (submodule.map_span b.repr.to_linear_map _) _,
                   rw [linear_map.range_eq_map, ← free_module_basis_spanning,
                       linear_map.map_span],
                   refine congr_arg _ _,
                   rw [← set.image_comp, ← set.range_comp],
                   ext, split, 
                   { rintro ⟨⟨i, j⟩, hij, h⟩, subst h,
                     refine ⟨⟨(i, j), hij⟩, _⟩,
                     simp only [function.comp_app, linear_map.sub_apply,
                                 finsupp.lmap_domain_apply, finsupp.map_domain_single,
                                 linear_equiv.coe_to_linear_map, linear_equiv.map_sub,
                                 basis.repr_self] },
                   { rintro ⟨⟨⟨i, j⟩, hij⟩, h⟩, subst h,
                     refine ⟨(i, j), hij, _⟩,
                     simp only [linear_equiv.coe_to_linear_map, function.comp_app,
                                 linear_equiv.map_sub, basis.repr_self, linear_map.sub_apply,
                                 finsupp.lmap_domain_apply, finsupp.map_domain_single] } }
  in ⟨i2.trans i1.symm.to_linear_equiv⟩.

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
