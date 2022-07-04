import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

def simplex_category.squash (n : ℕ) : simplex_category.mk n ⟶ simplex_category.mk 0 :=
  simplex_category.mk_hom ⟨(λ _, 0), by { intros x y _, reflexivity }⟩

-- def simplex_category.vertex (n : ℕ) (i : fin (n + 1))
--   : simplex_category.mk 0 ⟶ simplex_category.mk n :=
--   @simplex_category.mk_hom 0 n ⟨(λ _, i), (λ _ _ _, refl _)⟩

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

instance topologica_simplex.point_unique : unique (topological_simplex 0) := {
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

noncomputable
def inclusion (n : ℕ) : topological_simplex n ⟶ topological_simplex (n + 1) := 
  simplex_category.to_Top.map (simplex_category.δ 0)

noncomputable 
def const (n : ℕ) : topological_simplex n ⟶ topological_simplex (n + 1) :=
  simplex_category.to_Top.map (simplex_category.squash n
                                ≫ simplex_category.const (simplex_category.mk (n+1)) 0)

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

lemma const_desc (n : ℕ) (x : topological_simplex n) : const n x = vertex (n+1) 0 :=
begin
  delta const,
  delta vertex,
  rw simplex_category.to_Top.map_comp,
  simp, congr,
  apply @unique.eq_default _ topologica_simplex.point_unique
end

lemma coface_map_misses_output (n : ℕ) (i : fin (n + 2)) (j : simplex_category.mk n) :
  simplex_category.δ i j ≠ i :=
  fin.succ_above_ne i j

lemma succ_sigma_of_nonzero (n : ℕ) (k : simplex_category.mk (n + 1)) (h : k ≠ 0) 
  : fin.succ (simplex_category.σ 0 k) = k :=
begin
  cases k with k hk,
  cases k, contradiction, refl
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

