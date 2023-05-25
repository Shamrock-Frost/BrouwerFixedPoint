import algebraic_topology.simplex_category
import analysis.convex.topology

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

instance {n : ℕ} : has_zero (simplex_category.mk n) := ⟨⟨0, nat.zero_lt_succ _⟩⟩

-- might be some reason this doesn't exist already?
instance {ι} [fintype ι] : compact_space (std_simplex ℝ ι) :=
  is_compact_iff_compact_space.mp (is_compact_std_simplex ι)