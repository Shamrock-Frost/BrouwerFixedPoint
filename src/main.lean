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
      else unit_interval.to_nnreal (unit_interval.symm t)
      * x.val (simplex_category.σ 0 k),
begin
  dsimp [simplex_category.to_Top_obj],
  rw finset.sum_ite,
  transitivity unit_interval.to_nnreal t
             + finset.univ.sum (λ k, unit_interval.to_nnreal (unit_interval.symm t) * x.val k),
  { apply congr_arg2, 
    { rw finset.sum_const,
      transitivity 1 • unit_interval.to_nnreal t, 
      { congr,
        rw finset.card_eq_one,
        existsi (0 : simplex_category.mk (n + 1)),
        ext, simp },
      { simp } },
    { rw sum_over_n_simplices_eq, refl } },
  { transitivity (unit_interval.to_nnreal t) + unit_interval.to_nnreal (unit_interval.symm t) * 1, 
    { congr, cases x with x hx, dsimp [simplex_category.to_Top_obj] at hx, rw ← hx,
      symmetry, simp,
      apply @map_sum nnreal _ nnreal _ _ (nnreal →+ nnreal) _ 
                     (distrib_mul_action.to_add_monoid_hom nnreal (unit_interval.to_nnreal
                                                                  (unit_interval.symm t))) },
    { cases t, simp [unit_interval.symm, unit_interval.to_nnreal] } }
end⟩

lemma q_map_on_zero (n : ℕ) (t : unit_interval) (x : topological_simplex n) 
  : @coe_fn _ _ (simplex_category.to_Top_obj.has_coe_to_fun (simplex_category.mk (n + 1)))
                (q_map n t x) 0 = unit_interval.to_nnreal t := rfl

lemma q_map_on_nonzero (n : ℕ) (t : unit_interval) (x : topological_simplex n)
  (k : simplex_category.mk (n + 1)) (h : k ≠ 0)
  : @coe_fn _ _ (simplex_category.to_Top_obj.has_coe_to_fun (simplex_category.mk (n + 1))) 
                (q_map n t x) k
  = unit_interval.to_nnreal (unit_interval.symm t) * x.val (simplex_category.σ 0 k) :=
  by { dsimp [q_map, coe_fn],
       dsimp [simplex_category.to_Top_obj.has_coe_to_fun],
       rw ite_eq_right_iff, intro, contradiction }

lemma q_continuous (n : ℕ) : continuous (function.uncurry (q_map n)) :=
begin
  apply @continuous_subtype_mk (simplex_category.mk (n+1) → nnreal)
                               (I × topological_simplex n) _ _ _
                               (λ p, (function.uncurry (q_map n) p).val)
                               (λ p, (function.uncurry (q_map n) p).property),
  apply continuous_pi,
  intro i, cases i with i hi,
  dsimp [function.uncurry, q_map],
  apply continuous_if_const; intro h,
  { apply continuous.fst', exact unit_interval.to_nnreal_continuous },
  { cases i with i, trivial,
    apply continuous.mul,
    { apply continuous.comp, exact unit_interval.to_nnreal_continuous,
      apply continuous.fst', exact unit_interval.continuous_symm },
    have := @continuous.cod_restrict
                (I × topological_simplex n) ℝ _ _
                (λ x, (x.snd.val (simplex_category.σ 0 ⟨i.succ, hi⟩)).val)
                (λ x, x ≥ 0) _
                (λ x, (x.snd.val (simplex_category.σ 0 ⟨i.succ, hi⟩)).property),
    apply continuous.congr this,
    intro x, cases x, ext, refl,
    apply @continuous.snd' _ _ _ _ _ _
                          (λ x : (topological_simplex n),
                              (x.val (simplex_category.σ 0 ⟨i.succ, hi⟩)).val),
    apply continuous_induced_dom.comp,
    have : continuous (λ (x : simplex_category.mk n → nnreal),
                          x (simplex_category.σ 0 ⟨i.succ, hi⟩)),
    apply continuous_apply,
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
  { rw q_map_on_nonzero,
    simp [inclusion],
    symmetry, apply finset.sum_eq_single_of_mem,
    { simp, ext, refl },
    { intros b hb H,
      exfalso,
      cases b with b hb',
      simp at hb,
      apply H, rw ← hb,
      refl },
    { intro H, apply nat.succ_ne_zero j, apply congr_arg subtype.val H } }
end

lemma q_map_one_left (n : ℕ) (x : topological_simplex n)
  : q_map n 1 x = const n x :=
begin
  rw const_desc, apply eq_vertex, refl
end

def q (n : ℕ) : continuous_map.homotopy (inclusion n) (const n) := {
  to_fun := function.uncurry (q_map n),
  continuous_to_fun := q_continuous n,
  map_zero_left' := q_map_zero_left n,
  map_one_left' := q_map_one_left n
}

lemma q_surj (n : ℕ) : function.surjective (function.uncurry (q_map n)) :=
begin
  intro x,
  by_cases (x.val 0 = 1),
  { existsi ((1 : unit_interval), vertex n 0),
    dsimp [function.uncurry],
    rw q_map_one_left,
    symmetry,
    rw const_desc,
    apply eq_vertex,
    assumption },
  { have denom_pos : 0 < 1 - (x.val 0).val,
    { rw [lt_sub, sub_zero],
      apply lt_of_le_of_ne,
      apply topological_simplex.coord_le_one,
      intro h', apply h,
      simp at h', exact h' },
    have denom_desc : ↑ (1 - x.val 0) = 1 - (x.val 0).val,
    { rw [nnreal.sub_def],
      apply real.coe_to_nnreal,
      apply le_of_lt, apply denom_pos },
    have denom_nonzero : 1 - x.val 0 ≠ 0,
    { intro h, replace h := congr_arg coe h, 
      rw denom_desc at h,
      apply ne_of_lt denom_pos,
      rw h, refl },
    let t : unit_interval := ⟨x.val 0, (x.val 0).property, topological_simplex.coord_le_one _ _ _⟩,
    let y' : simplex_category.mk n → nnreal := λ i, x.val (i + 1) / (1 - x.val 0),
    have : finset.univ.sum y' = 1,
    { rw ← div_self denom_nonzero,
      rw eq_div_iff denom_nonzero,
      rw finset.sum_mul,
      apply nnreal.eq,
      rw denom_desc,
      rw eq_sub_iff_add_eq,
      rw [← nnreal.coe_to_real_hom, map_sum, nnreal.coe_to_real_hom],
      transitivity ↑(finset.univ.sum x.val),
      { rw [← nnreal.coe_to_real_hom, map_sum, nnreal.coe_to_real_hom],
        rw ← finset.insert_erase (finset.mem_univ (0 : simplex_category.mk (n+1))),
        rw finset.sum_insert (finset.not_mem_erase _ _),
        rw add_comm, 
        apply congr_arg2, refl,
        rw sum_over_n_simplices_eq,
        apply finset.sum_congr,
        { ext, rw finset.mem_filter, simp },
        { intros k hk,
          rw finset.mem_erase at hk, simp at hk,
          rw div_mul_cancel _ denom_nonzero,
          congr,
          symmetry, transitivity, symmetry, exact succ_sigma_of_nonzero n k hk,
          simp } },
      rw (_ : finset.univ.sum x.val = 1), refl, 
      exact x.property },
    let y : topological_simplex n := ⟨y', this⟩,
    existsi (t, y),
    dsimp [function.uncurry],
    ext k,
    by_cases (k = 0),
    { rw h, refl },
    { rw q_map_on_nonzero _ _ _ _ h,
      simp [y, unit_interval.symm, unit_interval.to_nnreal],
      rw [← @subtype.val_eq_coe _ _ x, denom_desc, mul_comm,
          ← nnreal.val_eq_coe (x.val 0), div_mul_cancel _ (ne.symm (ne_of_lt denom_pos))],
      congr,
      apply succ_sigma_of_nonzero, assumption } }
end

lemma q_quot (n : ℕ) : quotient_map (function.uncurry (q_map n)) := 
begin
  apply surjection_of_compact_hausdorff_is_quot_map,
  apply q_surj,
  apply q_continuous
end

-- lemma singular_homology.homotopy_invariant (n : ℕ) (X Y : Top) (f g : X ⟶ Y) 
--   (H : continuous_map.homotopy f g) : (singular_homology n).map f = (singular_homology n).map g :=
-- sorry