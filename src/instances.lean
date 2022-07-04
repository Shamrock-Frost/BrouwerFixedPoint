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
    rw ← is_compact_iff_is_compact_univ,
    dsimp [simplex_category.to_Top_obj],
    rw metric.compact_iff_closed_bounded,
    split,
    { change is_closed (finset.univ.sum ⁻¹' {(1 : nnreal)}),
      apply is_closed.preimage,
      { continuity },
      { rw (_ : {(1 : nnreal)} = subtype.val ⁻¹' {(1 : ℝ)}),
        { apply is_closed.preimage continuous_subtype_val (t1_space.t1 _),
          apply_instance },
        { ext, simp } } },
    { refine iff.mpr (metric.bounded_iff_subset_ball 0) _, 
      existsi (1 : ℝ),
      intros f hf,
      simp [metric.closed_ball],
      rw dist_pi_le_iff,
      { intro k,
        change (nndist (f k) 0 ≤ 1),
        rw nnreal.nndist_zero_eq_val',
        rw (_ : f = (⟨f, hf⟩ : topological_simplex n).val),
        apply topological_simplex.coord_le_one,
        reflexivity },
      linarith }
}⟩

instance (n : ℕ) : t2_space (topological_simplex n) := subtype.t2_space

def unit_interval.to_nnreal : unit_interval → nnreal := λ t, ⟨t.val, unit_interval.nonneg t⟩

@[continuity]
lemma unit_interval.to_nnreal_continuous : continuous unit_interval.to_nnreal :=
continuous_inclusion (λ x hx, and.left hx)

@[simp] lemma unit_interval.to_nnreal_zero : unit_interval.to_nnreal 0 = 0 := rfl

@[simp] lemma unit_interval.to_nnreal_one : unit_interval.to_nnreal 1 = 1 := rfl
