import algebraic_topology.simplex_category
import algebraic_topology.simplicial_object
import analysis.convex.basic
import algebraic_topology.simplicial_set

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

noncomputable theory

namespace simplex_category

def squash (n : ℕ) : simplex_category.mk n ⟶ simplex_category.mk 0 :=
  simplex_category.mk_hom ⟨(λ _, 0), by { intros x y _, reflexivity }⟩

def to_Top'_obj (x : simplex_category) := std_simplex ℝ x

open_locale simplicial big_operators classical

instance (x : simplex_category) : has_coe_to_fun x.to_Top'_obj (λ _, x → ℝ) :=
⟨λ f, (f : x → ℝ)⟩

lemma to_Top'_obj_coord_sum_nonzero {x : simplex_category} {s : finset x}
  (p : x.to_Top'_obj) : 0 ≤ ∑ i in s, p i := 
  le_of_eq_of_le (finset.sum_eq_zero (λ _ _, rfl)).symm
                 (finset.sum_le_sum (λ i _, p.property.left i))

@[ext]
lemma to_Top'_obj.ext {x : simplex_category} (f g : x.to_Top'_obj) :
  (f : x → ℝ) = g → f = g := subtype.ext

-- Should be defined in analysis.convex.basic, maybe?
def to_Top'_map {x y : simplex_category} (f : x ⟶ y)
  : x.to_Top'_obj → y.to_Top'_obj :=
    λ p, ⟨λ i, ∑ j in (finset.univ.filter (λ k, f k = i)), p j,
          λ i, to_Top'_obj_coord_sum_nonzero p,
          by { refine eq.trans _ p.2.right,
                refine eq.trans (finset.sum_bUnion _).symm _,
                { refine finset.pairwise_disjoint_coe.mp _,
                  convert set.pairwise_disjoint_fiber f _,
                  ext, simp },
                { apply finset.sum_congr,
                  { rw finset.eq_univ_iff_forall,
                    intro i,
                    rw finset.mem_bUnion,
                    exact ⟨f i, by simp, by simp⟩ },
                  { intros, refl } } }⟩

@[simp]
lemma coe_to_Top'_map {x y : simplex_category} (f : x ⟶ y) (g : x.to_Top'_obj) (i : y) :
  to_Top'_map f g i = ∑ j in (finset.univ.filter (λ k, f k = i)), g j := rfl

@[continuity]
lemma continuous_to_Top'_map {x y : simplex_category} (f : x ⟶ y) :
  continuous (to_Top'_map f) :=
continuous_subtype_mk _ $ continuous_pi $ λ i, continuous_finset_sum _ $
  λ j hj, continuous.comp (continuous_apply _) continuous_subtype_val

@[simps]
def to_Top' : simplex_category ⥤ Top :=
{ obj := λ x, Top.of x.to_Top'_obj,
  map := λ x y f, ⟨to_Top'_map f⟩,
  map_id' := begin
    intros x,
    ext f i : 3,
    change (finset.univ.filter (λ k, k = i)).sum _ = _,
    simp [finset.sum_filter]
  end,
  map_comp' := begin
    intros x y z f g,
    ext h i : 3,
    dsimp,
    erw ← finset.sum_bUnion,
    apply finset.sum_congr,
    { exact finset.ext (λ j, ⟨λ hj, by simpa using hj, λ hj, by simpa using hj⟩) },
    { tauto },
    { refine finset.pairwise_disjoint_coe.mp _,
      convert set.pairwise_disjoint_fiber f _,
      ext, simp },
  end }

end simplex_category

def Top.to_sSet' : Top ⥤ sSet :=
category_theory.colimit_adj.restricted_yoneda simplex_category.to_Top'

def topological_simplex (n : ℕ) := simplex_category.to_Top'_obj (simplex_category.mk n)

def topological_simplex.point : topological_simplex 0 := ⟨(λ _, 1), by {
  split, { intro, exact zero_le_one },
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
    { intro, ext x,
      cases x with k hk, simp at hk, subst hk,
      exact eq.trans (this a) (this topological_simplex.point).symm },
    rintro ⟨f, h⟩,
    exact eq.trans finset.sum_singleton.symm h.right }
}

noncomputable
def inclusion (n : ℕ) : Top.of (topological_simplex n) ⟶ Top.of (topological_simplex (n + 1)) := 
  simplex_category.to_Top'.map (simplex_category.δ 0)

noncomputable
def const_vertex (n : ℕ) (i : simplex_category.mk (n + 1))
  : Top.of (topological_simplex n) ⟶ Top.of (topological_simplex (n + 1)) :=
  simplex_category.to_Top'.map (simplex_category.squash n
                               ≫ simplex_category.const (simplex_category.mk (n+1)) i)

noncomputable
def vertex (n : ℕ) (i : simplex_category.mk n) : topological_simplex n 
  := simplex_category.to_Top'.map (simplex_category.const (simplex_category.mk n) i)
                                  topological_simplex.point

lemma topological_simplex.coord_le_one (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) : x.val i ≤ 1 :=
begin
  transitivity (finset.univ.sum x.val),
  { rw ← finset.insert_erase (finset.mem_univ i),
    rw finset.sum_insert (finset.not_mem_erase _ _),
    refine le_of_eq_of_le (add_zero _).symm _,
    apply add_le_add, refl,
    apply simplex_category.to_Top'_obj_coord_sum_nonzero },
  { exact le_of_eq x.property.right }
end

lemma topological_simplex.has_one_implies_eq_zero (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) (h : x.val i = 1) : ∀ j, i ≠ j → x.val j = 0 :=
begin
  intros j hij,
  have : finset.sum (insert i (insert j (finset.erase (finset.erase finset.univ i) j))) x.val = 1,
  { rw ← x.property.right, congr, rw [finset.insert_erase, finset.insert_erase],
    apply finset.mem_univ,
    apply finset.mem_erase_of_ne_of_mem,
    symmetry, assumption,
    apply finset.mem_univ },
  rw [finset.sum_insert, finset.sum_insert] at this,
  { rw h at this,
    rw add_right_eq_self at this,
    refine le_antisymm _ (x.property.left j),
    refine le_of_le_of_eq _ this,
    refine le_add_of_nonneg_right _,
    apply simplex_category.to_Top'_obj_coord_sum_nonzero },
  simp, simp, assumption
end

lemma vertex_coord_one (n : ℕ) (i : simplex_category.mk n) : 
  @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) i = 1 := 
begin
  simp [vertex],
  transitivity finset.univ.sum (λ _, (1 : ℝ)),
  congr, 
  { refine finset.eq_univ_of_forall _, intro x, simp, refl },
  { norm_num }
end

lemma vertex_coord_zero (n : ℕ) (i j : simplex_category.mk n) (h : i ≠ j) :
  @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) j = 0 :=
topological_simplex.has_one_implies_eq_zero n i _ (vertex_coord_one n i) j h

lemma eq_vertex (n : ℕ) (i : simplex_category.mk n) (x : topological_simplex n)
  : x.val i = 1 → x = vertex n i :=
begin
  intros hi,
  ext k,
  by_cases (i = k),
  { subst h, rw vertex_coord_one, rw ← hi, refl },
  { rw vertex_coord_zero n _ _ h,
    exact topological_simplex.has_one_implies_eq_zero n i x hi _ h }
end

lemma const_desc (n : ℕ) (i : simplex_category.mk (n + 1)) (x : topological_simplex n)
  : const_vertex n i x = vertex (n+1) i :=
begin
  delta const_vertex,
  delta vertex,
  rw simplex_category.to_Top'.map_comp,
  simp, congr,
  apply @unique.eq_default _ topological_simplex.point_unique
end

lemma deg_zero_zeroth_coface_map_is_vertex_one 
  : simplex_category.to_Top'_map (simplex_category.δ 0) topological_simplex.point
  = vertex 1 1 :=
by {
  transitivity const_vertex 0 1 topological_simplex.point,
  { congr, ext, cases x with x hx, cases x,
    refl, exfalso, simp at hx, assumption },
  { apply const_desc } 
}

lemma deg_zero_oneth_coface_map_is_vertex_zero
  : simplex_category.to_Top'_map (simplex_category.δ 1) topological_simplex.point
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