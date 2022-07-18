import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex
import analysis.convex.basic

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

def simplex_category.squash (n : ℕ) : simplex_category.mk n ⟶ simplex_category.mk 0 :=
  simplex_category.mk_hom ⟨(λ _, 0), by { intros x y _, reflexivity }⟩

noncomputable
def topological_simplex (n : ℕ) := simplex_category.to_Top.obj (simplex_category.mk n)

def topological_simplex.point : topological_simplex 0 := ⟨(λ _, 1), by {
  dsimp [simplex_category.to_Top_obj],
  apply finset.sum_eq_single_of_mem,
  exact finset.mem_univ 0,
  intros b h h', cases b with b bh, 
  exfalso, cases b, trivial, simp at bh, 
  assumption
}⟩

instance topological_simplex.point_unique : unique (topological_simplex 0) := {
  default := topological_simplex.point,
  uniq := by {
    suffices : ∀ x : topological_simplex 0, x.val 0 = 1,
    { intro, apply subtype.eq, funext x,
      cases x with k hk, simp at hk, subst hk,
      transitivity (1 : nnreal), 
      { rw ← this, refl },
      { rw ← this, refl } },
    intro x, cases x with f h,
    dsimp [simplex_category.to_Top_obj] at h,
    rw ← h,
    dsimp [subtype.val],
    symmetry,
    apply finset.sum_eq_single_of_mem, apply finset.mem_univ,
    intros b hb H,
    cases b with b h', exfalso, apply H, apply subtype.eq,
    simp at ⊢ h', assumption
  }
}

-- Should probably use this in more places?
noncomputable
def topological_simplex_alt (n : ℕ) := Top.of (std_simplex ℝ (fin (n + 1)))

def topological_simplex_alt_desc (n : ℕ) : topological_simplex n ≃ₜ topological_simplex_alt n := {
  to_fun := λ x, ⟨λ i, (x.val i).val, λ i, (x.val i).property,
                    by { have := (congr_arg subtype.val x.property),
                        refine eq.trans _ this,
                        symmetry, 
                        simp at this,
                        have := map_sum (⟨subtype.val, _, _⟩ : nnreal →+ ℝ) x.val finset.univ,
                        swap, { refl }, swap, { rintros ⟨x, _⟩ ⟨y, _⟩, simp },
                        refine eq.trans this _,
                        congr }⟩,
  inv_fun := λ x, ⟨λ i, ⟨x.val i, x.property.left i⟩,
                     by { refine subtype.eq _,
                         have := x.property.right,
                         refine eq.trans _ this,
                         let f : fin (n + 1) → nnreal := λ i, ⟨x.val i, x.property.left i⟩,
                         have := map_sum (⟨subtype.val, _, _⟩ : nnreal →+ ℝ) f finset.univ,
                         swap, { refl }, swap, { rintros ⟨x, _⟩ ⟨y, _⟩, simp },
                         refine eq.trans this _,
                         congr }⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  continuous_to_fun := by { simp, continuity,
                            apply continuous.congr ((continuous_apply i).comp continuous_subtype_coe), 
                            simp },
  continuous_inv_fun := by { simp, continuity,
                             apply continuous.congr ((continuous_apply i).comp continuous_subtype_coe), 
                             simp }
}

noncomputable
def inclusion (n : ℕ) : topological_simplex n ⟶ topological_simplex (n + 1) := 
  simplex_category.to_Top.map (simplex_category.δ 0)

noncomputable
def const_vertex (n : ℕ) (i : simplex_category.mk (n + 1))
  : topological_simplex n ⟶ topological_simplex (n + 1) :=
  simplex_category.to_Top.map (simplex_category.squash n
                                ≫ simplex_category.const (simplex_category.mk (n+1)) i)

noncomputable
def vertex (n : ℕ) (i : simplex_category.mk n) : topological_simplex n 
  := simplex_category.to_Top.map (simplex_category.const (simplex_category.mk n) i)
                                 topological_simplex.point

lemma topological_simplex.coord_le_one (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) : x.val i ≤ 1 :=
begin
  transitivity (finset.univ.sum x.val),
  { rw ← finset.insert_erase (finset.mem_univ i),
    rw finset.sum_insert (finset.not_mem_erase _ _),
    exact le_self_add },
  { exact le_of_eq x.property }
end

lemma topological_simplex.has_one_implies_eq_zero (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) (h : x.val i = 1) : ∀ j, i ≠ j → x.val j = 0 :=
begin
  intros j hij,
  have : finset.sum (insert i (insert j (finset.erase (finset.erase finset.univ i) j))) x.val = 1,
  { have := x.property, dsimp [simplex_category.to_Top_obj] at this, 
    rw ← this, congr, rw [finset.insert_erase, finset.insert_erase],
    apply finset.mem_univ,
    apply finset.mem_erase_of_ne_of_mem,
    symmetry, assumption,
    apply finset.mem_univ },
  rw [finset.sum_insert, finset.sum_insert] at this,
  { rw h at this,
    rw add_right_eq_self at this,
    rw ← @real.to_nnreal_coe (x.val j),
    apply real.to_nnreal_of_nonpos,
    rw ← real.le_to_nnreal_iff_coe_le,
    transitivity (0 : nnreal), rw ← this,
    apply le_add_of_nonneg_right,
    simp, simp },
  simp, simp, assumption
end

lemma vertex_coord_one (n : ℕ) (i : simplex_category.mk n) : 
  @coe_fn _ _ (simplex_category.to_Top_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) i = 1 := 
begin
  simp [vertex],
  transitivity finset.univ.sum (λ _, (1 : nnreal)),
  congr, 
  { apply finset.eq_univ_of_forall,
    intro x, simp, refl },
  { apply_instance },
  { norm_num }
end

lemma vertex_coord_zero (n : ℕ) (i j : simplex_category.mk n) (h : i ≠ j) :
  @coe_fn _ _ (simplex_category.to_Top_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) j = 0 :=
topological_simplex.has_one_implies_eq_zero n i _ (vertex_coord_one n i) j h

lemma eq_vertex (n : ℕ) (i : simplex_category.mk n) (x : topological_simplex n)
  : x.val i = 1 → x = vertex n i :=
begin
  intros hi,
  ext k,
  by_cases (i = k),
  { subst h, rw vertex_coord_one, rw ← hi, refl },
  { rw vertex_coord_zero n _ _ h, congr,
    exact topological_simplex.has_one_implies_eq_zero n i x hi _ h }
end

lemma const_desc (n : ℕ) (i : simplex_category.mk (n + 1)) (x : topological_simplex n)
  : const_vertex n i x = vertex (n+1) i :=
begin
  delta const_vertex,
  delta vertex,
  rw simplex_category.to_Top.map_comp,
  simp, congr,
  apply @unique.eq_default _ topological_simplex.point_unique
end

lemma deg_zero_zeroth_coface_map_is_vertex_one 
  : simplex_category.to_Top_map (simplex_category.δ 0) topological_simplex.point
  = vertex 1 1 :=
by {
  transitivity const_vertex 0 1 topological_simplex.point,
  { congr, ext, cases x with x hx, cases x,
    refl, exfalso, simp at hx, assumption },
  { apply const_desc } 
}

lemma deg_zero_oneth_coface_map_is_vertex_zero
  : simplex_category.to_Top_map (simplex_category.δ 1) topological_simplex.point
  = vertex 1 0 :=
by {
  transitivity const_vertex 0 0 topological_simplex.point,
  { congr, ext, cases x with x hx, cases x,
    refl, exfalso, simp at hx, assumption },
  { apply const_desc } 
}

lemma coface_map_misses_output (n : ℕ) (i : fin (n + 2)) (j : simplex_category.mk n) :
  simplex_category.δ i j ≠ i :=
  fin.succ_above_ne i j

lemma succ_sigma_of_nonzero (n : ℕ) (k : simplex_category.mk (n + 1)) (h : k ≠ 0) 
  : fin.succ (simplex_category.σ 0 k) = k :=
begin
  cases k with k hk,
  cases k, contradiction, refl
end

lemma fourth_simplicial_identity_modified (n : ℕ)
  (j : fin (n + 2)) (i : simplex_category.mk (n + 1))
  (H : ¬ (j = 0 ∧ i = 0))
  : simplex_category.δ j (simplex_category.σ 0 i)
  = simplex_category.σ 0 (simplex_category.δ j.succ i) :=
begin
  by_cases j = 0,
  { subst h, rw not_and at H, specialize H rfl,
    have : i = simplex_category.δ 0 (simplex_category.σ 0 i),
    { symmetry, apply succ_sigma_of_nonzero, assumption },
    rw this,
    generalize : simplex_category.σ 0 i = i', clear H this i,
    transitivity simplex_category.δ 0
                    ((simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) i'),
    refl,
    rw simplex_category.δ_comp_σ_self, 
    transitivity (simplex_category.δ (fin.succ 0) ≫ simplex_category.σ 0)
                    (simplex_category.δ 0 i'),
    rw simplex_category.δ_comp_σ_succ, refl, refl },
  { transitivity (simplex_category.σ 0 ≫ simplex_category.δ j) i, refl,
    rw ← simplex_category.δ_comp_σ_of_gt, 
    { refl },
    { apply lt_of_le_of_ne,
      apply fin.zero_le,
      apply ne.symm, dsimp,
      assumption } }
end

lemma sum_over_n_simplices_eq {G} [add_comm_monoid  G] (n : ℕ) (f : simplex_category.mk n → G) :
  finset.univ.sum f = (finset.filter (λ i : simplex_category.mk (n + 1), i ≠ 0) finset.univ).sum
                                     (λ j, f (simplex_category.σ 0 j)) :=
@finset.sum_bij' G (simplex_category.mk n) (simplex_category.mk (n + 1)) _
                 finset.univ
                 (finset.filter (λ i : simplex_category.mk (n + 1), i ≠ 0) finset.univ)
                 f
                 (λ i, f (simplex_category.σ 0 i))
                 (λ i _, simplex_category.δ 0 i) 
                 (λ x h, finset.mem_filter.mpr ⟨finset.mem_univ _, coface_map_misses_output n 0 x⟩)
                 (λ x h, congr_arg f (by {
                   transitivity (simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) x,
                   { rw simplex_category.δ_comp_σ_self, refl },
                   { refl } }))
                 (λ j _, simplex_category.σ 0 j)
                 (λ j _, finset.mem_univ _)
                 (λ i h, by { transitivity (simplex_category.δ (fin.cast_succ 0)
                                            ≫ simplex_category.σ 0) i,
                              refl,
                              rw simplex_category.δ_comp_σ_self, refl })
                 (λ j h, by { dsimp,
                              simp at h,
                              exact succ_sigma_of_nonzero n j h })

