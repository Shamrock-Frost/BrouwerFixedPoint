import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex
import .simplices
import topology.homotopy.basic

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

instance {n : ℕ} : has_zero (simplex_category.mk n) := ⟨⟨0, nat.zero_lt_succ _⟩⟩

instance : proper_space nnreal := ⟨by {
  intros,
  rw compact_iff_compact_in_subtype,
  rw subtype.coe_image,
  rw metric.compact_iff_closed_bounded,
  split,
  { have : is_closed ({ x : ℝ | 0 ≤ x } ∩ (metric.closed_ball x r)),
    { apply is_closed.inter, 
      { exact is_closed_ge' 0 },
      { exact metric.is_closed_ball } },
    apply eq.mp _ this, congr,
    ext, split,
    { intro h, existsi h.left, exact h.right },
    { intro h, cases h, exact ⟨h_w, h_h⟩ } },
  { rw metric.bounded_iff_subset_ball x.val,
    existsi r,
    intros y hy, cases hy with _ hy, simp at hy, 
    rw nnreal.dist_eq at hy, simp at hy, exact hy } }⟩

instance (n : ℕ) : compact_space (topological_simplex n) := 
⟨by {
    rw compact_iff_compact_in_subtype,
    rw (_ : coe '' set.univ = { f : (simplex_category.mk n) → nnreal | finset.sum finset.univ f = 1 }),
    { rw @metric.compact_iff_closed_bounded, split,
      { apply @is_closed.preimage _ _ _ _ (λ f, finset.univ.sum f) _ {(1 : nnreal)},
        { have := is_closed.preimage continuous_subtype_val (t1_space.t1 (1 : ℝ)),
          revert this, apply iff.mp,
          apply iff_of_eq, congr,
          ext, simp },
        continuity },
      apply iff.mpr (metric.bounded_iff_subset_ball 0), 
      existsi n,
       },
    { rw subtype.coe_image, ext, dsimp [simplex_category.to_Top_obj],  }
}⟩

def unit_interval.to_nnreal : unit_interval → nnreal := λ t, ⟨t.val, unit_interval.nonneg t⟩

@[continuity]
lemma unit_interval.to_nnreal_continuous : continuous unit_interval.to_nnreal :=
continuous_inclusion (λ x hx, and.left hx)

instance : has_coe_to_sort unit_interval nnreal := ⟨unit_interval.to_nnreal⟩

