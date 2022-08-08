import .homotopy_invariance

open category_theory

noncomputable
def singular_homology_of_base_to_of_pair (R : Type*) [comm_ring R] (n : ℕ)
  : arrow.right_func ⋙ singular_homology R n ⟶ singular_homology_of_pair R n := 
  (functor.associator arrow.right_func (singular_chain_complex R)
                      (homology_functor (Module R) (complex_shape.down ℕ) n)).inv
  ≫ whisker_right
      (whisker_left (singular_chain_complex R).map_arrow
                    (coker_functor_proj (chain_complex (Module R) ℕ)))
      (homology_functor (Module R) (complex_shape.down ℕ) n).

/-
Should move these lemmas
-/

lemma iso_of_four_term_exact_seq_start_zero_end_mono {V : Type*} [category V] [abelian V]
  {A B C D E : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D} {i : D ⟶ E}
  (e : exact_seq V [f, g, h, i]) (hf : f = 0) (hi : mono i) : is_iso g :=
begin
  apply_with is_iso_of_mono_of_epi {instances:=ff}, { apply_instance },
  { exact exact.mono_of_eq_zero ((exact_iff_exact_seq _ _).mpr (e.extract 0 2)) hf },
  { refine exact.epi_of_eq_zero ((exact_iff_exact_seq _ _).mpr (e.extract 1 2)) _, 
    exact (exact.mono_iff_eq_zero ((exact_iff_exact_seq _ _).mpr (e.extract 2 2))).mp hi } 
end

lemma injective_of_basis_to_basis_and_injective_on_basis {R : Type*} [ring R] [nontrivial R]
  {M N : Type*} [add_comm_group M] [add_comm_group N] [module R M] [module R N]
  {ι ι' : Type*} (bM : basis ι R M) (bN : basis ι' R N) (f : M →ₗ[R] N)
  (h1 : ∀ i, f (bM i) ∈ set.range bN) (h2 : ∀ i j, f (bM i) = f (bM j) → i = j)
  : function.injective f := 
begin
  rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
  intros m hm,
  rw ← basis.total_repr bM m at ⊢ hm,
  dsimp [finsupp.total] at hm,
  simp at hm,
  rw linear_independent_iff.mp _ (bM.repr m) hm, simp,

  let get_mapped_idx := λ i, classical.some (h1 i),
  have get_mapped_idx_spec : ∀ i, bN (get_mapped_idx i) = f (bM i) := 
    λ i, classical.some_spec (h1 i),
  simp_rw ← get_mapped_idx_spec,
  apply linear_independent.comp bN.linear_independent,
  intros i j h,
  apply h2,
  exact eq.trans (get_mapped_idx_spec i).symm (eq.trans (congr_arg bN h) (get_mapped_idx_spec j))
end

-- technically we don't need the nontrivial assumption
lemma contractible_subspace_homology_of_pair_map_is_iso (R : Type*) [comm_ring R] [nontrivial R] (A X : Top)
  (f : A ⟶ X) (hf : function.injective f)
  (hA : contractible_space A) (n : ℕ) (hn : n > 0)
  : is_iso ((singular_homology_of_base_to_of_pair R n).app (arrow.mk f)) :=
begin
  letI := (_ : mono ((singular_chain_complex R).map f)),
  swap,
  { apply_with homological_complex.mono_of_eval {instances:=ff}, 
    intro, rw Module.mono_iff_injective, apply singular_chain_complex_map_inj, assumption },
  have : exact_seq _ [↑((homology_functor (Module R) (complex_shape.down ℕ) n).map ((singular_chain_complex R).map f)),
                      ↑((homology_functor (Module R) (complex_shape.down ℕ) n).map
                        ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk ((singular_chain_complex R).map f)))),
                      ↑(homological_complex.δ ((singular_chain_complex R).map f)
                                              ((coker_functor_proj (chain_complex (Module R) ℕ)).app
                                                (arrow.mk ((singular_chain_complex R).map f))) _ n (n - 1) _),
                      ↑((homology_functor (Module R) (complex_shape.down ℕ) (n - 1)).map ((singular_chain_complex R).map f))]
       := (homological_complex.six_term_exact_seq ((singular_chain_complex R).map f)
                                                  ((coker_functor_proj (chain_complex (Module R) ℕ)).app
                                                    (arrow.mk ((singular_chain_complex R).map f)))
                                                  (coker_functor_degreewise_SES _)
                                                  n (n - 1) _).extract 0 4,
  swap, { rw complex_shape.down_rel, apply nat.sub_add_cancel, exact hn },
  convert iso_of_four_term_exact_seq_start_zero_end_mono this _ _,
  { exact category.id_comp _ },
  { apply limits.is_zero.eq_of_src,
    obtain ⟨zero_iso⟩ := homology_of_contractible_space R A hA n hn,
    apply limits.is_zero_of_iso_of_zero (limits.is_zero_zero _),
    exact zero_iso.symm,
    apply_instance },
  { by_cases n = 1,
    { subst h,
      rw nat.sub_self 1,
      rw Module.mono_iff_injective,
      refine injective_of_basis_to_basis_and_injective_on_basis (singular_homology0_basis R A)
                                                                (singular_homology0_basis R X)
                                                                ((homology_functor (Module R) (complex_shape.down ℕ) 0).map ((singular_chain_complex R).map f))
                                                                _ _,
      { intro a, induction a, existsi quot.mk (path_setoid X).r (f a),
        symmetry,
        convert singular_homology0_map_matrix R f a,
        refl },
      { intros a b hab, induction a, induction b,
        apply quot.sound,
        letI := hA, apply path_connected_space.joined,
        refl, refl } },
    { have h' : n - 1 > 0,
      { cases n, cases hn, cases n, contradiction,
        simp only [tsub_zero, nat.succ_pos', nat.succ_sub_succ_eq_sub, gt_iff_lt] },
      constructor, intros,
      apply limits.is_zero.eq_of_tgt,
       obtain ⟨zero_iso⟩ := homology_of_contractible_space R A hA (n - 1) h',
       apply limits.is_zero_of_iso_of_zero (limits.is_zero_zero _),
       exact zero_iso.symm,
       apply_instance } }
end.

noncomputable 
def singular_homology_connecting_homomorphism (R : Type*) [comm_ring R] (n : ℕ)
  {A X : Top} (f : A ⟶ X) (hf : function.injective f)
  : (singular_homology_of_pair R (n + 1)).obj (arrow.mk f) ⟶ (singular_homology R n).obj A :=
  homological_complex.δ ((singular_chain_complex R).map f)
                        ((coker_functor_proj (chain_complex (Module R) ℕ)).app
                          (arrow.mk ((singular_chain_complex R).map f)))
                          (@coker_functor_degreewise_SES _ _ _ _ _ _ _ _
                            (by { apply_with homological_complex.mono_of_eval {instances:=ff}, 
                                  intro, rw Module.mono_iff_injective,
                                  apply singular_chain_complex_map_inj, assumption }))
                          (n+1) n rfl.

lemma singular_homology_connecting_homomorphism_naturality (R : Type*) [comm_ring R] (n : ℕ)
  {A B X Y : Top} (f : A ⟶ X) (g : B ⟶ Y) (hf : function.injective f) (hg : function.injective g)
  (p : A ⟶ B) (q : X ⟶ Y) (w : p ≫ g = f ≫ q)
  : (singular_homology_of_pair R (n + 1)).map (arrow.hom_mk' w)
  ≫ singular_homology_connecting_homomorphism R n g hg
  = singular_homology_connecting_homomorphism R n f hf
  ≫ (singular_homology R n).map p :=
begin
  dsimp [singular_homology, singular_homology_of_pair, singular_homology_connecting_homomorphism],
  symmetry,
  have w' : (singular_chain_complex R).map f ≫ (singular_chain_complex R).map q
          = (singular_chain_complex R).map p ≫ (singular_chain_complex R).map g,
  { rw [← (singular_chain_complex R).map_comp, ← (singular_chain_complex R).map_comp, w] },
  apply δ_natural' _ _ _ _ _ ((singular_chain_complex R).map q), assumption,
  symmetry,
  exact (coker_functor_proj (chain_complex (Module R) ℕ)).naturality (arrow.hom_mk' w'.symm)
end.

lemma contractible_space_connecting_homomorphism_is_iso (R : Type*) [comm_ring R] [nontrivial R]
  (A X : Top) (f : A ⟶ X) (hf : function.injective f)
  (hX : contractible_space X) (n : ℕ) (hn : n > 0)
  : is_iso (singular_homology_connecting_homomorphism R n f hf) :=
begin
  have H : ∀ k > 0, limits.is_zero ((homology_functor (Module R) _ k).obj
                      ((singular_chain_complex R).obj X)),
  { intros k hk, 
    obtain ⟨zero_iso⟩ := homology_of_contractible_space R X hX k hk,
    apply limits.is_zero_of_iso_of_zero (limits.is_zero_zero _),
    exact zero_iso.symm,
    apply_instance },
  letI := (_ : mono ((singular_chain_complex R).map f)),
  swap,
  { apply_with homological_complex.mono_of_eval {instances:=ff}, 
    intro, rw Module.mono_iff_injective, apply singular_chain_complex_map_inj, assumption },
  have := (homological_complex.six_term_exact_seq ((singular_chain_complex R).map f)
                                                  ((coker_functor_proj (chain_complex (Module R) ℕ)).app
                                                    (arrow.mk ((singular_chain_complex R).map f)))
                                                  (coker_functor_degreewise_SES _)
                                                  (n + 1) n _).extract 1 3,
  swap, { exact eq.refl (n + 1) },
  apply_with is_iso_of_mono_of_epi {instances:=ff}, { apply_instance },
  { refine exact.mono_of_is_zero ((exact_iff_exact_seq _ _).mpr (this.extract 0 2)) _,
    apply H, exact nat.succ_pos' },
  { refine exact.epi_of_is_zero ((exact_iff_exact_seq _ _).mpr (this.extract 1 2)) _,
    apply H, assumption }
end.

