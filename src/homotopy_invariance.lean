import algebraic_topology.alternating_face_map_complex
import algebraic_topology.simplicial_set
import algebra.category.Module.abelian
import algebra.category.Module.adjunctions
import algebra.homology.homology
import algebra.homology.Module
import algebra.homology.homotopy
import topology.homotopy.basic
import algebraic_topology.simplex_category
import algebraic_topology.topological_simplex
import topology.constructions
import topology.algebra.group_with_zero
import topology.category.CompHaus.default
import topology.homotopy.product topology.homotopy.contractible
import analysis.convex.contractible
import data.opposite data.finset.pointwise
import .simplices .instances .general_topology .homological_algebra .linear_algebra 
import .acyclic_models_theorem .singular_homology_definitions

open category_theory algebraic_topology

notation `I` := unit_interval

section

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

-- The following proof is taken from Tom Dieck's book
def q_map (n : ℕ) (t : I) (x : topological_simplex n) : topological_simplex (n + 1) :=
⟨λ k, if k = 0
      then t
      else unit_interval.symm t * x.val (simplex_category.σ 0 k),
begin
  dsimp [topological_simplex, simplex_category.to_Top'_obj, std_simplex],
  rw finset.sum_ite,
  split,
  { intro k, split_ifs, exact t.property.left, 
    exact mul_nonneg (unit_interval.symm t).property.left (x.property.left _) },
  transitivity (t : ℝ) + finset.univ.sum (λ k, unit_interval.symm t * x.val k),
  { apply congr_arg2, 
    { rw finset.sum_const,
      refine eq.trans _ (one_smul ℕ _),
      congr,
      rw finset.card_eq_one,
      existsi (0 : simplex_category.mk (n + 1)),
      ext, simp },
    { rw sum_over_n_simplices_eq, refl } },
  { transitivity (t : ℝ) + unit_interval.symm t * 1, 
    { congr, cases x with x hx, rw ← hx.right,
      symmetry, apply finset.mul_sum },
    { cases t, simp [unit_interval.symm] } }
end⟩

lemma q_map_on_zero (n : ℕ) (t : unit_interval) (x : topological_simplex n) 
  : @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk (n + 1)))
                (q_map n t x) 0 = t := rfl

lemma q_map_on_nonzero (n : ℕ) (t : unit_interval) (x : topological_simplex n)
  (k : simplex_category.mk (n + 1)) (h : k ≠ 0)
  : @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk (n + 1))) 
                (q_map n t x) k
  = (unit_interval.symm t).val * x.val (simplex_category.σ 0 k) :=
  by { dsimp [q_map, coe_fn, simplex_category.to_Top'_obj.has_coe_to_fun],
       rw ite_eq_right_iff, intro, contradiction }

lemma q_continuous (n : ℕ) : continuous (function.uncurry (q_map n)) :=
begin
  apply continuous_subtype_mk,
  continuity, cases i with i hi,
  apply continuous_if_const; intro h,
  { continuity },
  { cases i with i, trivial,
    continuity,
    apply @continuous.snd' _ _ _ _ _ _
                          (λ x : topological_simplex n, x.val (simplex_category.σ 0 ⟨i.succ, hi⟩)),
    have : continuous (λ (x : simplex_category.mk n → ℝ), x (simplex_category.σ 0 ⟨i.succ, hi⟩)),
    { apply continuous_apply },
    apply continuous.congr (this.comp continuous_subtype_val),
    intro, refl }
end

lemma q_map_zero_left (n : ℕ) (x : topological_simplex n)
  : q_map n 0 x = inclusion n x :=
begin
  cases x with x hx,
  ext j, cases j with j hj, cases j with j,
  { transitivity (0 : ℝ), refl, symmetry,
    simp [inclusion],
    apply finset.sum_eq_zero,
    intros i H,
    exfalso, 
    refine fin.succ_ne_zero i _,
    simp at H, exact H },
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
  : q_map n 1 x = const_vertex n 0 x :=
begin
  rw const_desc, apply eq_vertex, refl
end

def q (n : ℕ) : continuous_map.homotopy (inclusion n) (const_vertex n 0) := {
  to_fun := function.uncurry (q_map n),
  continuous_to_fun := q_continuous n,
  map_zero_left' := q_map_zero_left n,
  map_one_left' := q_map_one_left n
}

noncomputable
def q_section (n : ℕ)
  : C({ σ : topological_simplex (n + 1) // σ.val 0 ≠ 1 }, I × topological_simplex n) := {
    to_fun := λ x,
      let t  : ℝ := x.val.val 0,
          ht : t ≠ 1 := x.property,
          y' : simplex_category.mk n → ℝ := λ i, x.val.val (i + 1) / (1 - t) in
      have t_le_one : t ≤ 1, from topological_simplex.coord_le_one (n+1) 0 x,
      have denom_pos : 0 < 1 - t, 
      from lt_of_le_of_ne (le_sub.mp (le_of_le_of_eq t_le_one (sub_zero 1).symm))
                          (λ h, ht (sub_eq_zero.mp h.symm).symm),
      have denom_nonzero : 1 - (t : ℝ) ≠ 0, from ne.symm (ne_of_lt denom_pos),
      have hy1 : ∀ i, 0 ≤ y' i, from λ i, div_nonneg (x.val.property.left _) (le_of_lt denom_pos),
      have hy2 : finset.univ.sum y' = 1,
      by { rw ← div_self denom_nonzero,
           rw eq_div_iff denom_nonzero,
           rw finset.sum_mul,
           rw eq_sub_iff_add_eq,
           refine eq.trans _ x.val.property.right,
           rw ← finset.insert_erase (finset.mem_univ (0 : simplex_category.mk (n + 1))),
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
      (⟨t, x.val.property.left 0, t_le_one⟩, ⟨y', (λ i, hy1 i), hy2⟩),
    continuous_to_fun := by {
      continuity,
      { refine continuous.congr (((continuous_apply 0).comp continuous_subtype_val).comp
                                                            continuous_subtype_val) _,
        intro, refl },
      change continuous
        (λ x, (λ x' : {σ : topological_simplex (n + 1) // σ.val 0 ≠ 1}, x'.val.val (i + 1)) x
            / (λ x' : {σ : topological_simplex (n + 1) // σ.val 0 ≠ 1}, 1 - x'.val.val 0) x),
      apply continuous.div,
      { refine continuous.congr (((continuous_apply (↑i + 1)).comp continuous_subtype_val).comp
                                                                   continuous_subtype_val) _,
        intro, refl },
      { suffices : continuous (λ x : simplex_category.mk (n + 1) → ℝ, 1 - x 0),
        { apply continuous.congr ((this.comp continuous_subtype_val).comp continuous_subtype_val),
          intro, refl },
        continuity },
      { intros x hx, exact x.property (sub_eq_zero.mp hx).symm }
    }
  }

lemma q_section_is_section (n : ℕ) (σ : topological_simplex (n + 1)) (h : σ.val 0 ≠ 1)
  : function.uncurry (q_map n) (q_section n ⟨σ, h⟩) = σ :=
begin
  dsimp [function.uncurry],
  ext k,
  by_cases h' : (k = 0),
  { rw h', refl },
  { rw q_map_on_nonzero _ _ _ _ h',
    simp [q_section, unit_interval.symm],
    rw [subtype.coe_mk, mul_comm, div_mul_cancel _ _],
    { congr, apply succ_sigma_of_nonzero, assumption },
    { intro h'', apply h, symmetry, rw ← sub_eq_zero, exact h'' } }
end

lemma q_section_on_preimage_of_image
  (n : ℕ) (p : I × topological_simplex n) (h : (function.uncurry (q_map n) p).val 0 ≠ 1)
  : q_section n ⟨function.uncurry (q_map n) p, h⟩ = p :=
begin
  cases p with t σ, ext,
  { simp [q_map, q_section] },
  { simp [q_section],
    change (q_map n t σ).val (fin.succ x) / (1 - t) = σ.val x,
    apply div_eq_of_eq_mul (λ h', h.symm (sub_eq_zero.mp h')),
    transitivity, apply q_map_on_nonzero n t σ (fin.succ x) (fin.succ_ne_zero x),
    simp [q_map], rw mul_comm, congr,
    exact eq.trans (fin.pred_above_zero (fin.succ_ne_zero x)) (fin.pred_succ _) }
end

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
  { exact ⟨q_section n ⟨x, h⟩, q_section_is_section n x h⟩ }
end

lemma q_quot (n : ℕ) : quotient_map (function.uncurry (q_map n)) := 
begin
  -- why doesn't this get found by typeclass instance resolution :(
  have : compact_space (I × topological_simplex n),
  { dsimp [topological_simplex, simplex_category.to_Top'_obj], apply_instance },
  apply @surjection_of_compact_hausdorff_is_quot_map _ _ _ _ this,
  apply q_surj,
  apply q_continuous
end

lemma q_fiber_desc {n : ℕ} {x y : I × topological_simplex n}
  (H : function.uncurry (q_map n) x = function.uncurry (q_map n) y)
  : (x.fst = (1 : unit_interval) ∧ y.fst = (1 : unit_interval)) ∨ x = y :=
begin
  cases x with t a, cases y with s b,
  dsimp, dsimp [function.uncurry] at H,
  cases t with t ht, cases s with s hs,
  have : t = s,
  { change ((q_map n ⟨t, ht⟩ a).val 0 = (q_map n ⟨s, hs⟩ b).val 0),
    congr, assumption },
  by_cases (t = 1),
  { left, split; ext; simp, assumption, rw ← this, assumption },
  { right, simp, split, assumption,
    transitivity (q_section n ⟨function.uncurry (q_map n) (⟨t, ht⟩, a), h⟩).snd,
    { symmetry, exact congr_arg prod.snd (q_section_on_preimage_of_image n (⟨t, ht⟩, a) h) },
    { have h' := this.subst h,
      transitivity (q_section n ⟨function.uncurry (q_map n) (⟨s, hs⟩, b), h'⟩).snd,
      { congr' 3 },
      { exact congr_arg prod.snd (q_section_on_preimage_of_image n (⟨s, hs⟩, b) h') } } }
end

lemma q_of_coface {n : ℕ} (j : fin (n + 2))
  (t : unit_interval) (x : topological_simplex n)
  : q_map (n + 1) t (simplex_category.to_Top'_map (simplex_category.δ j) x)
  = simplex_category.to_Top'_map (simplex_category.δ j.succ) (q_map n t x) :=
begin
  ext k : 2, by_cases (k = 0),
  { subst h,
    rw q_map_on_zero,
    simp only [fin.coe_eq_cast_succ, simplex_category.coe_to_Top'_map],
    transitivity ({0} : finset (simplex_category.mk (n + 1))).sum (q_map n t x).val,
    { rw finset.sum_singleton, refl },
    { congr, symmetry,
      rw finset.eq_singleton_iff_unique_mem,
      split,
      { rw finset.mem_filter, 
        simp only [true_and, finset.mem_univ],
        refine (fin.succ_above_eq_zero_iff _).mpr rfl,
        apply fin.succ_ne_zero },
      { intros k hk, 
        rw finset.mem_filter at hk,
        refine (fin.succ_above_eq_zero_iff _).mp hk.right,
        apply fin.succ_ne_zero } } },
  { rw q_map_on_nonzero _ _ _ _ h,
    simp only [fin.coe_eq_cast_succ, simplex_category.coe_to_Top'_map, subtype.val_eq_coe],
    dsimp [simplex_category.to_Top'_map],
    rw finset.mul_sum,
    refine @finset.sum_bij' ℝ (simplex_category.mk n) (simplex_category.mk (n + 1)) _
                            _ _
                            _ _
                            (λ t _, simplex_category.δ 0 t) --i
                            _
                            _
                            (λ t _, simplex_category.σ 0 t) --j
                            _
                            _
                            _,
    { intros i hi,
      simp only [true_and, finset.mem_univ, finset.mem_filter] at hi ⊢,
      transitivity (simplex_category.δ 0 ≫ simplex_category.δ (fin.succ j)) i,
      refl,
      rw simplex_category.δ_comp_δ (fin.zero_le _),
      transitivity simplex_category.δ 0 (simplex_category.σ 0 k),
      rw ← hi,
      refl,
      exact succ_sigma_of_nonzero _ k h },
    { intros i hi, simp, split_ifs,
      { exfalso, apply coface_map_misses_output, assumption },
      { congr, symmetry,
        transitivity (simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) i, refl,
        rw simplex_category.δ_comp_σ_self, refl } },
    { intros i hi,
      simp only [true_and, finset.mem_univ, finset.mem_filter] at hi ⊢,
      rw ← hi,
      apply fourth_simplicial_identity_modified,
      intro H, cases H with H1 H2, subst H1, subst H2,
      apply h, rw ← hi, refl },
    { intros i hi,
      simp only [true_and, finset.mem_univ, finset.mem_filter],
      transitivity (simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) i, refl,
      rw simplex_category.δ_comp_σ_self, refl },
    { intros i hi, 
      simp only [true_and, finset.mem_univ, finset.mem_filter] at hi ⊢,
      apply succ_sigma_of_nonzero,
      intro h', apply h,
      rw ← hi, rw h',
      apply fin.succ_above_ne_zero_zero,
      apply fin.succ_ne_zero } }
end

end

section

noncomputable
def ε_map (R : Type*) [comm_ring R] {X : Top} (x0 : X) : Π (n : ℕ),
  ((singular_chain_complex R).obj X).X n → ((singular_chain_complex R).obj X).X n
| 0 := λ x, finsupp.sum x (λ _ n, n • simplex_to_chain (singular_zero_simplex_of_pt x0) R)
| _ := 0

noncomputable
def ε_hom (R : Type*) [comm_ring R] {X : Top} (x0 : X) (n : ℕ) : 
  ((singular_chain_complex R).obj X).X n ⟶ ((singular_chain_complex R).obj X).X n := {
    to_fun := ε_map R x0 n,
    map_add' := by { intros, cases n; dsimp [ε_map],
      { apply finsupp.sum_add_index',
        { intro, simp },
        { intros, apply add_smul } },
      { rw zero_add } },
    map_smul' := by {
      intros, cases n; dsimp [ε_map],
      { rw [finsupp.smul_sum, finsupp.sum_smul_index'],
        congr, ext, rw smul_assoc,
        intro, apply zero_smul },
      symmetry, apply smul_zero }
  }

noncomputable
def ε (R : Type*) [comm_ring R] {X : Top} (x0 : X) 
  : (singular_chain_complex R).obj X ⟶ (singular_chain_complex R).obj X := {
  f := ε_hom R x0,
  comm' := by {
    intros i j h, simp at h, subst h,
    cases j; ext σ σ'; simp [ε_hom, ε_map],
    { rw singular_chain_complex_differential_desc_deg_0,
      rw finsupp.sum_sub_index,
      { symmetry, rw sub_eq_zero, dsimp [simplex_to_chain],
        rw [finsupp.sum_single_index, finsupp.sum_single_index]; simp },
      { intros, rw sub_mul } } }
}

noncomputable 
def cone_construction_lift_simplex {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (σ : Top.of (topological_simplex i) ⟶ X) : Top.of (topological_simplex (i + 1)) ⟶ X :=
  let σ' : (Top.of (I × topological_simplex i)) ⟶ (Top.of (I × X)) :=
        category_theory.functor.map cylinder.{0} σ,
      Hσ' : Top.of (I × topological_simplex i) ⟶ X := σ' ≫ H.to_continuous_map
    in @lift_along_quot_map (Top.of (I × topological_simplex i)) (Top.of (topological_simplex (i + 1))) X
                            ⟨function.uncurry (q_map i), q_continuous i⟩
                            Hσ' (q_quot i)
                            (by { intros x y Hxy,
                                  cases q_fiber_desc Hxy,
                                  { dsimp [Hσ', σ', cylinder],
                                    rw [h.left, h.right],
                                    transitivity, apply H.map_one_left',
                                    symmetry, transitivity, apply H.map_one_left',
                                    refl },
                                  { rw h } })

noncomputable
def cone_construction_hom (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  : ((singular_chain_complex R).obj X).X i ⟶ ((singular_chain_complex R).obj X).X (i + 1) :=
  (Module.free R).map (cone_construction_lift_simplex x0 H i)

noncomputable
def cone_construction_complex_hom (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (i j : ℕ) : ((singular_chain_complex R).obj X).X i ⟶ ((singular_chain_complex R).obj X).X j :=
  if h : i + 1 = j
  -- Should make this use eq_to_hom
  then @eq.rec _ _ (λ n, ((singular_chain_complex R).obj X).X i
                      ⟶ ((singular_chain_complex R).obj X).X n)
               (cone_construction_hom R x0 H i) _ h
  else 0

lemma cone_construction_hom_on_face {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (j : fin (i + 2))
  (σ : Top.of (topological_simplex (i + 1)) ⟶ X)
  : cone_construction_lift_simplex x0 H i
                                   (simplex_category.to_Top'.map (simplex_category.δ j) ≫ σ)
  = simplex_category.to_Top'.map (simplex_category.δ j.succ)
  ≫ cone_construction_lift_simplex x0 H (i + 1) σ :=
begin
  ext p, simp,
  cases (q_surj i p) with p',
  subst h,
  transitivity H (p'.fst, σ (simplex_category.to_Top'.map (simplex_category.δ j) p'.snd)),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                     (Top.of (topological_simplex (i + 1))) X
                                     ⟨function.uncurry (q_map i), q_continuous i⟩
                                     _ _ _
                                     (function.uncurry (q_map i) p')
                                     _
                                     _,
    refl },
  { symmetry,
    refine @lift_along_quot_map_spec (Top.of (I × topological_simplex (i+1)))
                                     (Top.of (topological_simplex (i + 2))) X
                                     ⟨function.uncurry (q_map (i + 1)), q_continuous (i + 1)⟩
                                     _ _ _
                                     (simplex_category.to_Top'_map (simplex_category.δ j.succ)
                                                                  (function.uncurry (q_map i) p'))
                                     (p'.fst, simplex_category.to_Top'.map (simplex_category.δ j)
                                                                          p'.snd)
                                     _,
    cases p' with p1 p2, simp,
    apply q_of_coface }
end

lemma cone_construction_hom_at_vertex {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (σ : Top.of (topological_simplex i) ⟶ X)
  : (cone_construction_lift_simplex x0 H i σ) (vertex (i + 1) 0)
  = x0 :=
begin
  transitivity H (1, σ (vertex i 0)),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                     (Top.of (topological_simplex (i + 1))) X
                                     ⟨function.uncurry (q_map i), q_continuous i⟩
                                     _ _ _ (vertex (i + 1) 0) ((1 : unit_interval), vertex i 0) _,
    simp, rw q_map_one_left, 
    rw const_desc },
  { transitivity, exact H.map_one_left' _, refl }
end

lemma cone_construction_complex_hom_desc_base {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (p : topological_simplex i) (σ : Top.of (topological_simplex i) ⟶ X)
  : (cone_construction_lift_simplex x0 H i σ) (inclusion i p) 
  = σ p :=
begin
  transitivity H (0, σ p),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                     (Top.of (topological_simplex (i + 1))) X
                                     ⟨function.uncurry (q_map i), q_continuous i⟩
                                     _ _ _ (inclusion i p) ((0 : unit_interval), p) _,
    simp, rw q_map_zero_left },
  { transitivity, exact H.map_zero_left' _, refl }
end

lemma cone_construction_comm_zero (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (σ : Top.of (topological_simplex 0) ⟶ X)
  : finsupp.single σ 1
  = d_next 0 (cone_construction_complex_hom R x0 H) (finsupp.single σ 1)
  + prev_d 0 (cone_construction_complex_hom R x0 H) (finsupp.single σ 1)
  + simplex_to_chain (singular_zero_simplex_of_pt x0) R :=
begin
  simp,
  dsimp [cone_construction_complex_hom],
  split_ifs, swap, contradiction,
  dsimp [cone_construction_hom],
  rw finsupp.map_domain_single,
  rw singular_chain_complex_differential_desc_deg_0,
  dsimp [simplex_to_chain],
  rw [sub_eq_add_neg, add_assoc, add_comm (-_), ← sub_eq_add_neg],
  rw (sub_eq_zero.mpr _),
  { rw add_zero, congr,
    apply @continuous_map.ext (topological_simplex 0),
    rw unique.forall_iff,
    dsimp [default],
    rw deg_zero_zeroth_coface_map_is_vertex_one,
    rw (_ : vertex _ _ = inclusion 0 topological_simplex.point),
    { rw cone_construction_complex_hom_desc_base },
    { symmetry, exact deg_zero_zeroth_coface_map_is_vertex_one } },
  { congr,
    apply @continuous_map.ext (topological_simplex 0),
    rw unique.forall_iff,
    dsimp [default],
    rw deg_zero_oneth_coface_map_is_vertex_zero,
    rw cone_construction_hom_at_vertex,
    refl }
end

lemma cone_construction_comm_higher_deg (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (i : ℕ) (σ : Top.of (topological_simplex (i + 1)) ⟶ X)
  : finsupp.single σ 1
  = d_next (i + 1) (cone_construction_complex_hom R x0 H) (finsupp.single σ 1)
  + prev_d (i + 1) (cone_construction_complex_hom R x0 H) (finsupp.single σ 1) :=
begin
  simp,
  dsimp [cone_construction_complex_hom],
  split_ifs, swap, contradiction,
  symmetry, rw ← eq_sub_iff_add_eq',
  transitivity, exact congr_arg _ finsupp.map_domain_single,
  rw singular_chain_complex_differential_desc,
  rw fin.sum_univ_succ,
  rw sub_eq_add_neg, apply congr_arg2,
  { simp [simplex_to_chain],
    congr,
    ext p,
    apply cone_construction_complex_hom_desc_base },
  { rw [singular_chain_complex_differential_desc, map_sum],
    rw ← finset.sum_neg_distrib,
    congr,
    ext j,
    rw linear_map.map_smul_of_tower, 
    apply congr_fun, apply congr_arg,
    rw ← neg_smul,
    apply congr_arg2,
    { rw fin.coe_succ,
      rw pow_succ,
      simp only [neg_mul, one_mul, eq_self_iff_true, neg_inj] },
    { delta simplex_to_chain,
      symmetry, transitivity, exact finsupp.map_domain_single,
      apply congr_fun, apply congr_arg,
      apply cone_construction_hom_on_face } }
end

noncomputable
def cone_construction (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  : homotopy (homological_complex.id _) (ε R x0) := {
    hom := cone_construction_complex_hom R x0 H,
    zero' := by { intros i j h, dsimp at h, dsimp [cone_construction_complex_hom],
                  split_ifs, contradiction, refl }, 
    comm := by {
      intros, ext σ : 2, dsimp [homological_complex.id],
      cases i; dsimp [ε, ε_hom, ε_map],
      { rw [finsupp.sum_single_index, one_smul],
        apply cone_construction_comm_zero,
        apply zero_smul },
      { rw [add_zero],
        apply cone_construction_comm_higher_deg }
    }
  }

end

section

universe u

local attribute [instance] category_theory.limits.has_zero_object.has_zero

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

open category_theory.limits

lemma homology_of_contractible_space (R : Type*) [comm_ring R] (X : Top) (h : contractible_space X)
  : ∀ (i : ℕ), 0 < i → is_isomorphic ((singular_homology R i).obj X) 0 := 
begin
  intros i h,
  apply iso_zero_of_id_eq_zero,
  transitivity (homology_functor _ _ i).map
    (homological_complex.id ((singular_chain_complex R).obj X)),
  symmetry, apply category_theory.functor.map_id,
  cases (id_nullhomotopic X) with x0 H,
  cases H with H,
  rw homology_map_eq_of_homotopy (cone_construction R x0 H),
  cases i, { exfalso, exact lt_irrefl _ h },
  apply homology_at_ith_index_zero,
  ext, simp,
  dsimp [ε, ε_hom, ε_map],
  refl 
end

noncomputable
def singular_chain_complex_basis (R : Type*) [comm_ring R]
  : complex_functor_basis (singular_chain_complex R) := 
  λ n, { indices := unit,
         models := λ _, Top.of (topological_simplex n),
         basis_elem := λ _, simplex_to_chain (𝟙 (Top.of (topological_simplex n))) R,
         lin_indep := λ X, let g : (Top.of (topological_simplex n) ⟶ X)
                                 → ((singular_chain_complex R).obj X).X n
                                 := λ f, ((singular_chain_complex R).map f).f n
                                           (simplex_to_chain (𝟙 (Top.of (topological_simplex n))) R),
                               e : (Σ (i : unit), Top.of (topological_simplex n) ⟶ X)
                                 ≃ (Top.of (topological_simplex n) ⟶ X) :=
                                 equiv.trans (equiv.sigma_equiv_prod unit _)
                                              (equiv.punit_prod _) in
                           have H : linear_independent R g,
                           by { have : g = (λ f, simplex_to_chain f R),
                                { apply funext, intro f,
                                  transitivity, apply finsupp.map_domain_single,
                                  apply congr_fun, apply congr_arg,
                                  ext, refl },
                                rw this,
                                dsimp [simplex_to_chain],
                                apply free_module_basis_linear_independent },
                           (linear_independent_equiv' e.symm rfl).mp H,
         spanning := λ X, by { transitivity submodule.span R (set.range (λ f, (finsupp.single f (1 : R)))),
                               { congr, ext, split,
                                 { rintro ⟨i, f, h⟩,
                                   existsi f,
                                   rw ← h, symmetry,
                                   transitivity, apply finsupp.map_domain_single, 
                                   congr, ext, refl },
                                 { rintro ⟨f, h⟩,
                                   existsi unit.star, existsi f,
                                   rw ← h, 
                                   transitivity, apply finsupp.map_domain_single, 
                                   congr, ext, refl } },
                                 apply free_module_basis_spanning } }

lemma prod_of_contractible_contractible (X Y : Type*) [topological_space X] [topological_space Y]
  (hX : contractible_space X) (hY : contractible_space Y) : contractible_space (X × Y) := 
begin
  rw contractible_iff_id_nullhomotopic at *,
  rcases hX with ⟨x0, ⟨H_X⟩⟩, rcases hY with ⟨y0, ⟨H_Y⟩⟩,
  existsi (x0, y0),
  have : continuous_map.homotopic _ _ :=
    ⟨continuous_map.homotopy.prod ((continuous_map.homotopy.refl ⟨@prod.fst X Y⟩).hcomp H_X)
                                  ((continuous_map.homotopy.refl ⟨@prod.snd X Y⟩).hcomp H_Y)⟩,
  refine eq.mp _ this,
  congr; ext; cases a; refl
end

def inclusion_at_t_nat_trans (t : unit_interval) : category_theory.functor.id Top ⟶ cylinder := {
  app := λ X, ⟨λ x, (t, x), by continuity⟩
}

lemma inclusion_at_t_nat_trans_on_chain (R : Type*) [comm_ring R]
  (t : unit_interval) (n : ℕ)
  : ((singular_chain_complex R).map
     ((inclusion_at_t_nat_trans t).app 
       ((singular_chain_complex_basis R n).models unit.star))).f n
          ((singular_chain_complex_basis R n).basis_elem unit.star)
  = simplex_to_chain ⟨prod.mk t, by continuity⟩ R :=
begin
  delta singular_chain_complex, delta free_complex_on_sset,
  simp,
  delta singular_chain_complex_basis,
  simp [simplex_to_chain],
  refl
end

lemma inclusion_at_0_nat_trans_app_comp_homotopy (R : Type*) [comm_ring R]
  {X Y : Top} {f g : X ⟶ Y} (H : continuous_map.homotopy f g)
  : (whisker_right (inclusion_at_t_nat_trans 0) (singular_chain_complex R)).app X
    ≫ (singular_chain_complex R).map H.to_continuous_map
  = (singular_chain_complex R).map f := 
  eq.trans ((singular_chain_complex R).map_comp ((inclusion_at_t_nat_trans 0).app X)
                                                H.to_continuous_map).symm
           (congr_arg (@category_theory.functor.map _ _ _ _ (singular_chain_complex R) X Y)
                      (continuous_map.ext H.map_zero_left'))

lemma inclusion_at_1_nat_trans_app_comp_homotopy (R : Type*) [comm_ring R]
  {X Y : Top} {f g : X ⟶ Y} (H : continuous_map.homotopy f g)
  : (whisker_right (inclusion_at_t_nat_trans 1) (singular_chain_complex R)).app X
    ≫ (singular_chain_complex R).map H.to_continuous_map
  = (singular_chain_complex R).map g := 
  eq.trans ((singular_chain_complex R).map_comp ((inclusion_at_t_nat_trans 1).app X)
                                                H.to_continuous_map).symm
           (congr_arg (@category_theory.functor.map _ _ _ _ (singular_chain_complex R) X Y)
                      (continuous_map.ext H.map_one_left'))

noncomputable 
def singular_homology.chain_homotopy_of_homotopy (R : Type*) [comm_ring R]
  {X Y : Top} {f g : X ⟶ Y} (H : continuous_map.homotopy f g)
  : homotopy ((singular_chain_complex R).map f) ((singular_chain_complex R).map g) :=
  have h : whisker_right (whisker_right (inclusion_at_t_nat_trans 0) (singular_chain_complex R))
             (homology_functor (Module R) (complex_shape.down ℕ) 0) =
           whisker_right (whisker_right (inclusion_at_t_nat_trans 1) (singular_chain_complex R))
             (homology_functor (Module R) (complex_shape.down ℕ) 0),
  by { apply functor_basis.homology_ext (singular_chain_complex_basis R 0),
       intro i, cases i,
       refine exists.intro (simplex_to_chain _ R) _,
       { refine ⟨(λ p, (⟨p.val 0, p.property.left 0, topological_simplex.coord_le_one 1 0 p⟩,
                         topological_simplex.point)), _⟩,
         continuity,
         apply continuous.congr
                 (continuous.comp (continuous_apply 0 : continuous (λ x : fin 2 → ℝ, x 0))
                                 continuous_subtype_val),
         intro x, cases x, simp },
       dsimp [simplex_to_chain],
       rw singular_chain_complex_differential_desc_deg_0,
       rw [inclusion_at_t_nat_trans_on_chain, inclusion_at_t_nat_trans_on_chain],
       delta simplex_category.to_Top',
       simp,
       rw add_sub_left_comm,
       refine eq.trans (add_zero _).symm _,
       congr,
       { ext, simp [simplex_category.to_Top'_map],
         transitivity ((∅ : finset (fin 1)).sum (λ i, x.val i)),
         simp, refl,
         simp, congr,
         apply @unique.eq_default _ topological_simplex.point_unique },
       { symmetry, rw sub_eq_zero, congr,
         ext : 3, simp [simplex_category.to_Top'_map],
         refine eq.trans x.property.right.symm _,
         congr,
         simp, 
         apply @unique.eq_default _ topological_simplex.point_unique } },
  let s := (lift_nat_trans_unique
             (singular_chain_complex_basis R)
             (cylinder ⋙ singular_chain_complex R)
             (λ n hn, 
               have H : ∀ k, contractible_space (unit_interval × topological_simplex k),
               by { intro k, apply prod_of_contractible_contractible,
                     { apply convex.contractible_space,
                       apply @convex_Icc ℝ ℝ _ _ _ _ 0 1,
                       existsi (0 : ℝ), simp },
                     { apply convex.contractible_space,
                       { exact convex_std_simplex ℝ _ },
                       { exact ⟨(vertex k 1).val, (vertex k 1).property⟩ } } },
               let H' (k : ℕ) (hk : k > 0) (i : (singular_chain_complex_basis R k).indices) :=
                 homology_of_contractible_space R (Top.of (unit_interval × topological_simplex k))
                                                 (H k) n hn
               in ⟨H' n hn, H' (n + 1) (nat.zero_lt_succ n)⟩)
             (whisker_right (inclusion_at_t_nat_trans 0) (singular_chain_complex R))
             (whisker_right (inclusion_at_t_nat_trans 1) (singular_chain_complex R))
             h).to_chain_htpy X,
      s' := s.comp_right ((singular_chain_complex R).map H.to_continuous_map)
  in ((homotopy.of_eq (inclusion_at_0_nat_trans_app_comp_homotopy R H).symm).trans s').trans
        (homotopy.of_eq (inclusion_at_1_nat_trans_app_comp_homotopy R H))

lemma singular_homology.chain_homotopy_of_homotopy_natural (R : Type*) [comm_ring R]
  {A X B Y : Top} (i : A ⟶ X) (j : B ⟶ Y)
  (f' g' : A ⟶ B) (f g : X ⟶ Y)
  (w1 : f' ≫ j = i ≫ f) (w2 : g' ≫ j = i ≫ g)
  (H' : continuous_map.homotopy f' g') (H : continuous_map.homotopy f g)
  (h : cylinder.map i ≫ H.to_continuous_map = H'.to_continuous_map ≫ j)
  : homotopy.comp_right (singular_homology.chain_homotopy_of_homotopy R H')
                        ((singular_chain_complex R).map j)
  = (homotopy.of_eq (eq.trans ((singular_chain_complex R).map_comp f' j).symm
                                (eq.trans (congr_arg _ w1)
                                          ((singular_chain_complex R).map_comp i f)))).trans
      ((homotopy.comp_left (singular_homology.chain_homotopy_of_homotopy R H)
                           ((singular_chain_complex R).map i)).trans
        (homotopy.of_eq (eq.trans ((singular_chain_complex R).map_comp i g).symm 
                                  (eq.trans (congr_arg _ w2.symm)
                                            ((singular_chain_complex R).map_comp g' j))))) :=
begin
  ext p q : 3, simp [singular_homology.chain_homotopy_of_homotopy],
  by_cases h' : p + 1 = q,
  { rw [← homological_complex.comp_f, ← category_theory.functor.map_comp],
    rw ← h,
    rw [category_theory.functor.map_comp, homological_complex.comp_f, ← category.assoc,
        ← category_theory.functor.comp_map],
    rw ← (lift_nat_trans_unique (singular_chain_complex_basis R)
                                (cylinder ⋙ singular_chain_complex R) _ _ _ _).naturality,
    apply category.assoc,
    exact h' },
  { rw ← complex_shape.down_rel _ q p at h', rw [homotopy.zero _ _ _ h', homotopy.zero _ _ _ h'],
    simp }
end

lemma singular_homology.homotopy_invariant (R : Type*) [comm_ring R]
  (n : ℕ) {X Y : Top} {f g : X ⟶ Y} (H : continuous_map.homotopy f g)
  : (singular_homology R n).map f = (singular_homology R n).map g :=
  homology_map_eq_of_homotopy (singular_homology.chain_homotopy_of_homotopy R H) n

lemma singular_homology_of_pair.homotopy_invariant (R : Type*) [comm_ring R]
  (n : ℕ) (A X B Y : Top) (i : A ⟶ X) (j : B ⟶ Y)
  (f' g' : A ⟶ B) (f g : X ⟶ Y)
  (w1 : f' ≫ j = i ≫ f) (w2 : g' ≫ j = i ≫ g)
  (H' : continuous_map.homotopy f' g') (H : continuous_map.homotopy f g)
  (h : cylinder.map i ≫ H.to_continuous_map = H'.to_continuous_map ≫ j)
  : (singular_homology_of_pair R n).map (arrow.hom_mk w1 : arrow.mk i ⟶ arrow.mk j)
  = (singular_homology_of_pair R n).map (arrow.hom_mk w2 : arrow.mk i ⟶ arrow.mk j) :=
  homology_map_eq_of_homotopy
    (chain_homotopy_on_coker_of_compatible_chain_homotopies 
      ((singular_chain_complex R).map i) ((singular_chain_complex R).map j)
      ((singular_chain_complex R).map f') ((singular_chain_complex R).map g')
      ((singular_chain_complex R).map f) ((singular_chain_complex R).map g)
      (eq.trans ((singular_chain_complex R).map_comp f' j).symm
                (eq.trans (congr_arg _ w1) 
                          ((singular_chain_complex R).map_comp i f)))
      (eq.trans ((singular_chain_complex R).map_comp g' j).symm
                (eq.trans (congr_arg _ w2) 
                          ((singular_chain_complex R).map_comp i g)))
      (singular_homology.chain_homotopy_of_homotopy R H')
      (singular_homology.chain_homotopy_of_homotopy R H)
      (singular_homology.chain_homotopy_of_homotopy_natural R i j f' g' f g w1 w2 H' H h))
    n

end