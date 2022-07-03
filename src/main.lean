import algebraic_topology.alternating_face_map_complex
import algebraic_topology.simplicial_set
import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
import algebra.homology.homology
import topology.homotopy.basic
import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex
import topology.constructions
import topology.category.CompHaus.default
import .simplices .instances .general_topology

open category_theory algebraic_topology

noncomputable
def singular_homology (n : ℕ) : Top ⥤ Module ℤ :=
  Top.to_sSet
  ⋙ ((simplicial_object.whiskering _ _).obj (Module.free ℤ))
  ⋙ alternating_face_map_complex _
  ⋙ homology_functor _ _ n

notation `I` := Top.of unit_interval

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

-- The following proof is taken from Tom Dieck's book
def q_map (n : ℕ) (t : unit_interval) (x : topological_simplex n) : topological_simplex (n + 1) :=
⟨λ k, if k = 0
      then unit_interval.to_nnreal t
      else unit_interval.to_nnreal (unit_interval.symm t) * x.val (simplex_category.σ ⟨0, nat.zero_lt_succ n⟩ k),
begin
  dsimp [simplex_category.to_Top_obj],
  rw finset.sum_ite,
  transitivity unit_interval.to_nnreal t
             + finset.univ.sum (λ k : simplex_category.mk n, unit_interval.to_nnreal (unit_interval.symm t) * x.val k),
  { apply congr_arg2, 
    { rw finset.sum_const,
      transitivity 1 • unit_interval.to_nnreal t, 
      { congr,
        rw finset.card_eq_one,
        existsi (0 : simplex_category.mk (n + 1)),
        ext, simp },
      { simp } },
    { apply @finset.sum_bij nnreal (simplex_category.mk (n+1)) (simplex_category.mk n) _
                            (finset.filter (λ (x : simplex_category.mk (n + 1)), ¬x = 0) finset.univ)
                            finset.univ
                            (λ j, unit_interval.to_nnreal (unit_interval.symm t) * x.val (simplex_category.σ ⟨0, nat.zero_lt_succ n⟩ j))
                            (λ j, unit_interval.to_nnreal (unit_interval.symm t) * x.val j)
                            (λ j _, simplex_category.σ ⟨0, nat.zero_lt_succ n⟩ j),
      { intros, apply finset.mem_univ },
      { intros j h, simp * at h ⊢ },
      { intros j k hj hk h, cases j with j, cases k with k, 
        cases j with j, { exfalso, simp at hj, assumption },
        cases k with k, { exfalso, simp at hk, assumption },
        ext, simp at ⊢ h, exact subtype.ext_iff.mp h },
      { intros j _,
        existsi (simplex_category.δ ⟨0, nat.zero_lt_succ _⟩ j),
        cases j with j hj,
        existsi (finset.mem_filter.mpr ⟨finset.mem_univ _, _⟩),
        swap, intro h, apply nat.succ_ne_zero j, exact (subtype.ext_iff_val.mp h),
        ext, reflexivity } } },
  { transitivity (unit_interval.to_nnreal t) + unit_interval.to_nnreal (unit_interval.symm t) * 1,
    { congr, cases x with x hx, dsimp [simplex_category.to_Top_obj] at hx, rw ← hx,
      symmetry, simp,
      apply @map_sum nnreal _ nnreal _ _ (nnreal →+ nnreal) _ 
                     (distrib_mul_action.to_add_monoid_hom nnreal (unit_interval.to_nnreal (unit_interval.symm t))) },
    { cases t, simp [unit_interval.symm, unit_interval.to_nnreal] } }
end⟩

lemma q_continuous (n : ℕ) : continuous (function.uncurry (q_map n)) :=
begin
  apply @continuous_subtype_mk (simplex_category.mk (n+1) → nnreal) (I × topological_simplex n) _ _ _
                               (λ p, (function.uncurry (q_map n) p).val)
                               (λ p, (function.uncurry (q_map n) p).property),
  continuity,
  cases i with i hi,
  dsimp [function.uncurry, q_map],
  apply continuous_if_const; intro h,
  { continuity },
  { cases i with i, trivial,
    continuity,
    have := @continuous.cod_restrict (I × topological_simplex n) ℝ _ _
                                     (λ x, ((x.snd).val (simplex_category.σ 0 ⟨i.succ, hi⟩)).val)
                                     (λ x, x ≥ 0) _ _,
    swap 3, intro x,
    simp, exact (x.snd.val (simplex_category.σ 0 ⟨i.succ, hi⟩)).property,
    apply continuous.congr this,
    intro x, cases x, ext, refl,
    apply @continuous.snd' _ _ _ _ _ _ (λ x : (topological_simplex n), (x.val (simplex_category.σ 0 ⟨i.succ, hi⟩)).val),
    have : continuous (λ (x : simplex_category.mk n → nnreal), x (simplex_category.σ 0 ⟨i.succ, hi⟩)),
    continuity,
    exact continuous.comp this continuous_subtype_val }
end

lemma q_map_zero_left (n : ℕ) (x : topological_simplex n)
  : q_map n 0 x = inclusion n x :=
begin
  cases x with x hx,
  ext j, cases j with j hj, cases j with j,
  { transitivity (0 : ℝ), refl, symmetry,
    simp [inclusion], intros x H, cases x,
    rw subtype.ext_iff_val at H,
    exfalso, 
    exact nat.succ_ne_zero _ H },
  { simp [q_map, inclusion],
    dsimp [coe_fn, simplex_category.to_Top_obj.has_coe_to_fun],
    split_ifs,
    { exfalso, apply nat.succ_ne_zero, exact congr_arg subtype.val h },
    { dsimp [unit_interval.to_nnreal], transitivity, apply one_mul,
      transitivity, symmetry, 
      apply @finset.sum_singleton _ _ _ x,
      congr, symmetry, rw finset.eq_singleton_iff_unique_mem,
      split,
      { rw finset.mem_filter, split, apply finset.mem_univ,
        apply subtype.eq,
        destruct (simplex_category.σ 0 ⟨j.succ, hj⟩),
        intros y hy H,
        transitivity (simplex_category.δ 0 (simplex_category.σ 0 ⟨j.succ, hj⟩)).val,
        refl,
        rw H,
        transitivity y.succ, refl,
        symmetry, exact congr_arg nat.succ (congr_arg subtype.val H) },
      { intros x hx, cases x with x hx', ext,
        simp at hx,
        transitivity j,
        refine (@nat.succ_inj' x j).mp _,
        refine eq.trans _ (subtype.ext_iff_val.mp hx),
        refl,
        refl } } }
end

lemma q_map_one_left (n : ℕ) (x : topological_simplex n)
  : q_map n 1 x = const n x :=
begin
  ext j, destruct j, intros j' hj H, cases j' with j', 
  { subst H,
    transitivity (1 : ℝ), refl,
    simp [const],
    transitivity (finset.univ.sum x.val).val, symmetry,
    transitivity (1 : nnreal).val, congr, exact x.property, refl,
    congr, ext, rw finset.mem_filter,
    simp, refl },
  { simp [q_map, const], transitivity (0 : nnreal), 
    { transitivity ite (j = 0) (unit_interval.to_nnreal 1) (unit_interval.to_nnreal 0 * x.val (simplex_category.σ 0 j)), 
      refl,
      rw ite_eq_iff, right,
      split, 
      { intro h, apply nat.succ_ne_zero j',
        transitivity j.val,
        symmetry, exact congr_arg subtype.val H,
        exact congr_arg subtype.val h },
      { simp, left, refl } },
    { transitivity finset.empty.sum x.val,
      symmetry, exact finset.sum_empty,
      congr,
      symmetry, apply finset.eq_empty_of_forall_not_mem,
      intros k hk,
      simp at hk,
      apply nat.succ_ne_zero j', symmetry,
      transitivity j.val,
      rw ← hk, refl,
      rw H } }
end

def q (n : ℕ) : continuous_map.homotopy (inclusion n) (const n) := {
  to_fun := function.uncurry (q_map n),
  continuous_to_fun := q_continuous n,
  map_zero_left' := q_map_zero_left n,
  map_one_left' := q_map_one_left n
}

lemma q_quot (n : ℕ) : quotient_map (function.uncurry (q_map n)) := 
begin
  apply quotient_map_of_is_closed_map,
  { intro x,
    by_cases (x.val 0 = 1), admit,
    -- { existsi ((1 : unit_interval), vertex n 0),
    --   ext j, apply congr_arg, destruct j, intros j' hj H,
    --   rw q_map_one_left,
    --   simp [const],
    --   cases j',
    --   { subst H, transitivity (1 : nnreal),
    --     transitivity finset.univ.sum (vertex n 0).val,
    --     { congr, ext, simp, refl },
    --     exact (vertex n 0).property,
    --     symmetry, exact h },
    --   { symmetry, transitivity,
    --     apply topological_simplex.has_one_implies_eq_zero (n+1) 0 x h j,
    --     { intro h', apply nat.succ_ne_zero j', symmetry, rw H at h', exact congr_arg subtype.val h' },
    --     { transitivity (∅ : finset (simplex_category.mk n)).sum (vertex n 0).val,
    --       symmetry, apply finset.sum_empty,
    --       congr,
    --       ext, simp,
    --       intro h', have : 0 = j := h',
    --       rw H at this, apply nat.succ_ne_zero j',
    --       symmetry, exact congr_arg subtype.val this } } },
    { let t := x.val 0,
      -- todo: need to convert t to a unit_interval, so we want 
      -- topological_simplex.eval : topological_simplex n → simplex_category.mk n → unit_interval
      -- and the map topological_simplex (n + 1) → topological_simplex n which drops the first coord
      -- and put this together to get t : unit_interval and x : topological_simplex n to (t, x/t)
      admit } },
  { apply @CompHaus.is_closed_map (CompHaus.of unit_interval) (CompHaus.of (topological_simplex n).α) ⟨function.uncurry (q_map n), sorry⟩,
     }
end

-- lemma singular_homology.homotopy_invariant (n : ℕ) (X Y : Top) (f g : X ⟶ Y) 
--   (H : continuous_map.homotopy f g) : (singular_homology n).map f = (singular_homology n).map g :=
-- sorry