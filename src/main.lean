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
import topology.category.CompHaus.default
import topology.homotopy.contractible
import data.opposite
import .simplices .instances .general_topology .homological_algebra .linear_algebra

open category_theory algebraic_topology

notation `I` := Top.of unit_interval

section

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

lemma q_fiber_desc {n : ℕ} {x y : I × topological_simplex n}
  (H : function.uncurry (q_map n) x = function.uncurry (q_map n) y)
  : (x.fst = (1 : unit_interval) ∧ y.fst = (1 : unit_interval)) ∨ x = y :=
begin
  cases x with t a, cases y with s b,
  dsimp, dsimp [function.uncurry] at H,
  cases t with t ht, cases s with s hs,
  have : t = s,
  { change (unit_interval.to_nnreal ⟨t, ht⟩).val = (unit_interval.to_nnreal ⟨s, hs⟩).val,
    apply congr_arg subtype.val,
    change ((q_map n ⟨t, ht⟩ a).val 0 = (q_map n ⟨s, hs⟩ b).val 0),
    congr, assumption },
  by_cases (t = 1),
  { left, split; ext; simp, assumption, rw ← this, assumption },
  { right, simp, split, assumption,
    ext j,
    have jth_coord_eq : (q_map n ⟨t, ht⟩ a).val ((simplex_category.δ 0) j)
                      = (q_map n ⟨s, hs⟩ b).val ((simplex_category.δ 0) j),
    { congr, assumption },
    dsimp [q_map] at jth_coord_eq,
    split_ifs at jth_coord_eq,
    { exfalso, apply fin.succ_ne_zero j, assumption },
    rw (_ : simplex_category.σ 0 (simplex_category.δ 0 j)
          = (simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) j)
        at jth_coord_eq,
    rw simplex_category.δ_comp_σ_self at jth_coord_eq,
    rw ← (_ : (⟨t, ht⟩ : unit_interval) = ⟨s, hs⟩) at jth_coord_eq,
    refine congr_arg subtype.val (mul_left_cancel₀ _ jth_coord_eq),
    { dsimp [unit_interval.symm, unit_interval.to_nnreal],
      rw subtype.ext_iff, simp,
      rw sub_eq_zero,
      apply ne.symm, assumption },
    { exact subtype.eq this }, { refl } }
end

lemma q_of_coface {n : ℕ} (j : fin (n + 2))
  (t : unit_interval) (x : topological_simplex n)
  : q_map (n + 1) t (simplex_category.to_Top_map (simplex_category.δ j) x)
  = simplex_category.to_Top_map (simplex_category.δ j.succ) (q_map n t x) :=
begin
  ext k : 2, by_cases (k = 0),
  { subst h,
    rw q_map_on_zero,
    simp only [fin.coe_eq_cast_succ, simplex_category.coe_to_Top_map],
    transitivity ({0} : finset (simplex_category.mk (n + 1))).sum (q_map n t x).val, --⇑(q_map n t x),
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
    simp only [fin.coe_eq_cast_succ, simplex_category.coe_to_Top_map, subtype.val_eq_coe],
    dsimp [simplex_category.to_Top_map],
    rw finset.mul_sum,
    refine @finset.sum_bij' nnreal (simplex_category.mk n) (simplex_category.mk (n + 1)) _
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
def free_complex_on_sset (R : Type*) [comm_ring R] : sSet ⥤ chain_complex (Module R) ℕ :=
  ((simplicial_object.whiskering _ _).obj (Module.free R)) ⋙ alternating_face_map_complex _

noncomputable
def singular_chain_complex (R : Type*) [comm_ring R] : Top ⥤ chain_complex (Module R) ℕ :=
  Top.to_sSet ⋙ free_complex_on_sset R

noncomputable
def singular_homology (R : Type*) [comm_ring R] (n : ℕ) : Top ⥤ Module R :=
  singular_chain_complex R ⋙ homology_functor _ _ n

noncomputable
def singular_zero_simplex_of_pt {X : Top} (x0 : X)
  : (Top.to_sSet.obj X).obj (opposite.op (simplex_category.mk 0)) := 
  (continuous_map.const (topological_simplex 0) x0)

noncomputable
def simplex_to_chain {n : ℕ} {X : sSet}
  (σ : X.obj (opposite.op (simplex_category.mk n)))
  (R : Type*) [comm_ring R] : ((free_complex_on_sset R).obj X).X n :=
  finsupp.single σ 1

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

open_locale big_operators

lemma singular_chain_complex_differential_desc (R : Type*) [comm_ring R] {X : Top} {n : ℕ}
  (σ : topological_simplex (n + 1) ⟶ X)
  : ((singular_chain_complex R).obj X).d (n + 1) n (finsupp.single σ 1)
  = ∑ (i : fin (n + 2)), (-1 : ℤ)^(i : ℕ)
  • simplex_to_chain (simplex_category.to_Top.map (simplex_category.δ i) ≫ σ) R := by {
    dsimp [singular_chain_complex, free_complex_on_sset],
    transitivity (alternating_face_map_complex.obj_d
                     (((simplicial_object.whiskering Type (Module R)).obj (Module.free R)).obj
                                                                         (Top.to_sSet.obj X)) n)
                     .to_fun
                     (finsupp.single σ 1),
    { congr, apply chain_complex.of_d },
    { simp [alternating_face_map_complex.obj_d],
      congr, ext i, congr,
      dsimp [simplex_to_chain],
      rw finsupp.eq_single_iff, split,
      { intros t h,
        rw finset.mem_singleton,
        simp at h,
        have : ((Module.free R).map ((Top.to_sSet.obj X).δ i) (finsupp.single σ 1)).to_fun t ≠ 0 := h,
        simp at this,
        exact and.left (finsupp.single_apply_ne_zero.mp this) },
      { change (((Module.free R).map ((Top.to_sSet.obj X).δ i) (finsupp.single σ 1)).to_fun
                  (simplex_category.to_Top.map (simplex_category.δ i) ≫ σ) = 1),
        simp,
        exact finsupp.single_eq_same } }
  }

lemma singular_chain_complex_differential_desc_deg_0 (R : Type*) [comm_ring R] {X : Top}
  (σ : topological_simplex 1 ⟶ X)
  : ((singular_chain_complex R).obj X).d 1 0 (finsupp.single σ 1)
  = simplex_to_chain (simplex_category.to_Top.map (@simplex_category.δ 0 0) ≫ σ) R 
  - simplex_to_chain (simplex_category.to_Top.map (@simplex_category.δ 0 1) ≫ σ) R :=
begin
  rw singular_chain_complex_differential_desc,
  rw finset.sum_eq_add_of_mem (0 : fin 2) 1 (finset.mem_univ _) (finset.mem_univ _),
  { simp, rw sub_eq_add_neg },
  { simp },
  { intros c H' H, exfalso, cases c with c hc, cases H,
    cases c, contradiction, cases c, contradiction,
    rw [nat.succ_lt_succ_iff, nat.succ_lt_succ_iff] at hc,
    exact not_lt_zero' hc }
end

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
  (σ : topological_simplex i ⟶ X) : topological_simplex (i + 1) ⟶ X :=
  let σ' : (Top.of (I × topological_simplex i)) ⟶ (Top.of (I × X)) :=
        category_theory.functor.map cylinder.{0} σ,
      Hσ' : Top.of (I × topological_simplex i) ⟶ X := σ' ≫ H.to_continuous_map
    in @lift_along_quot_map (Top.of (I × topological_simplex i)) (topological_simplex (i + 1)) X
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
  then @eq.rec _ _ (λ n, ((singular_chain_complex R).obj X).X i
                      ⟶ ((singular_chain_complex R).obj X).X n)
               (cone_construction_hom R x0 H i) _ h
  else 0

lemma cone_construction_hom_on_face {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (j : fin (i + 2))
  (σ : topological_simplex (i + 1) ⟶ X)
  : cone_construction_lift_simplex x0 H i
                                   (simplex_category.to_Top.map (simplex_category.δ j) ≫ σ)
  = simplex_category.to_Top.map (simplex_category.δ j.succ)
  ≫ cone_construction_lift_simplex x0 H (i + 1) σ :=
begin
  ext p, simp,
  cases (q_surj i p) with p',
  subst h,
  transitivity H (p'.fst, σ (simplex_category.to_Top.map (simplex_category.δ j) p'.snd)),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                    (topological_simplex (i + 1)) X
                                    ⟨function.uncurry (q_map i), q_continuous i⟩
                                    _ _ _
                                    (function.uncurry (q_map i) p')
                                    _
                                    _,
    refl },
  { symmetry,
    refine @lift_along_quot_map_spec (Top.of (I × topological_simplex (i+1)))
                                     (topological_simplex (i + 2)) X
                                     ⟨function.uncurry (q_map (i + 1)), q_continuous (i + 1)⟩
                                     _ _ _
                                     (simplex_category.to_Top_map (simplex_category.δ j.succ)
                                                                  (function.uncurry (q_map i) p'))
                                     (p'.fst, simplex_category.to_Top.map (simplex_category.δ j)
                                                                          p'.snd)
                                     _,
    cases p' with p1 p2, simp,
    apply q_of_coface }
end

lemma cone_construction_hom_at_vertex {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (σ : topological_simplex i ⟶ X)
  : (cone_construction_lift_simplex x0 H i σ) (vertex (i + 1) 0)
  = x0 :=
begin
  transitivity H (1, σ (vertex i 0)),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                     (topological_simplex (i + 1)) X
                                     ⟨function.uncurry (q_map i), q_continuous i⟩
                                     _ _ _ (vertex (i + 1) 0) ((1 : unit_interval), vertex i 0) _,
    simp, rw q_map_one_left, 
    rw const_desc },
  { transitivity, exact H.map_one_left' _, refl }
end

lemma cone_construction_complex_hom_desc_base {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (p : topological_simplex i) (σ : topological_simplex i ⟶ X)
  : (cone_construction_lift_simplex x0 H i σ) (inclusion i p) 
  = σ p :=
begin
  transitivity H (0, σ p),
  { refine @lift_along_quot_map_spec (Top.of (I × topological_simplex i))
                                     (topological_simplex (i + 1)) X
                                     ⟨function.uncurry (q_map i), q_continuous i⟩
                                     _ _ _ (inclusion i p) ((0 : unit_interval), p) _,
    simp, rw q_map_zero_left },
  { transitivity, exact H.map_zero_left' _, refl }
end

lemma cone_construction_comm_zero (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (σ : topological_simplex 0 ⟶ X)
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
  (i : ℕ) (σ : topological_simplex (i + 1) ⟶ X)
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

local attribute [instance] category_theory.limits.has_zero_object.has_zero

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

open category_theory.limits

lemma iso_zero_of_id_eq_zero (R : Type*) [comm_ring R] (M : Module R)
  (h : 𝟙 M = 0) : is_isomorphic M 0 :=
    ⟨is_zero.iso_zero (@Module.is_zero_of_subsingleton _ _ M
                         ⟨λ x y, calc x = (𝟙 M : M ⟶ M) x : rfl
                                    ... = (0 : M ⟶ M) x   : congr_fun (congr_arg _ h) x
                                    ... = (0 : M ⟶ M) y   : rfl
                                    ... = (𝟙 M : M ⟶ M) y : (congr_fun (congr_arg _ h) y).symm⟩)⟩

lemma homology_at_ith_index_zero {ι : Type*} (V : Type*) [category V] [has_zero_morphisms V]
                                 (c : complex_shape ι) [has_zero_object V] [has_equalizers V]
                                 [has_images V] [has_image_maps V] [has_cokernels V]
                                 {X Y : homological_complex V c}
                                 (f : X ⟶ Y) (i : ι) (H : f.f i = 0)
                                 : (homology_functor V c i).map f = 0 :=
begin
  simp,
  ext, simp,
  suffices : kernel_subobject_map (homological_complex.hom.sq_from f i) = 0,
  { rw this, simp },
  ext, simp,
  rw H, simp
end

lemma homology_of_contractible_space (R : Type*) (X : Top) [comm_ring R] [contractible_space X]
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
         models := λ _, topological_simplex n,
         basis_elem := λ _, simplex_to_chain (𝟙 (topological_simplex n)) R,
         lin_indep := λ X, let g : (topological_simplex n ⟶ X)
                                 → ((singular_chain_complex R).obj X).X n
                                 := λ f, ((singular_chain_complex R).map f).f n
                                           (simplex_to_chain (𝟙 (topological_simplex n)) R),
                               e : (Σ (i : unit), topological_simplex n ⟶ X)
                                 ≃ (topological_simplex n ⟶ X) :=
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
         spanning := λ X, by { transitivity submodule.span R (set.range (λ f,
                                    (finsupp.single f (1 : R)
                                    : (Module.free R).obj (topological_simplex n ⟶ X)))),
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

lemma singular_homology.homotopy_invariant (R : Type*) [comm_ring R]
  (n : ℕ) (X Y : Top) (f g : X ⟶ Y) (H : continuous_map.homotopy f g)
  : (singular_homology R n).map f = (singular_homology R n).map g :=
  lifts_of_nat_trans_H0_give_same_map_in_homology
    (singular_chain_complex_basis R)
    (cylinder ⋙ singular_chain_complex R)
    -- (λ n i, ⟨homology_of_contractible_space R (Top.of (I × topological_simplex (n + 1))) n, 
    --          homology_of_contractible_space⟩)

end