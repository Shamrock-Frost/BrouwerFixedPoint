import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

noncomputable
def topological_simplex (n : ℕ) := simplex_category.to_Top.obj (simplex_category.mk n)

noncomputable
def inclusion (n : ℕ) : topological_simplex n ⟶ topological_simplex (n + 1) := 
  simplex_category.to_Top.map (simplex_category.δ 0)

noncomputable 
def const (n : ℕ) : topological_simplex n ⟶ topological_simplex (n + 1) :=
  simplex_category.to_Top.map (@simplex_category.mk_hom n (n+1) ⟨(λ x, 0), (λ _ _ _, refl _)⟩)

noncomputable
def vertex (n : ℕ) (i : simplex_category.mk n) : topological_simplex n 
  := simplex_category.to_Top.map
        (@simplex_category.mk_hom 0 n
                                  ⟨(λ _, i), (λ _ _ _, refl _)⟩)
                                  ⟨(λ _, 1), by { dsimp [simplex_category.to_Top_obj],
                                                  transitivity finset.sum {(0 : simplex_category.mk 0)}
                                                                          (λ _ : simplex_category.mk 0, (1 : nnreal)),
                                                  congr, simp }⟩

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
