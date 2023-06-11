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
import topology.category.CompHaus.basic
import topology.homotopy.product topology.homotopy.contractible
import analysis.convex.contractible
import analysis.convex.topology
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
      ext, 
      simp only [finset.mem_filter, finset.mem_univ, true_and, finset.mem_singleton] },
    { rw sum_over_n_simplices_eq, refl } },
  { transitivity (t : ℝ) + unit_interval.symm t * 1, 
    { congr, cases x with x hx, rw ← hx.right,
      symmetry, apply finset.mul_sum },
    { cases t,
      simp only [unit_interval.symm, subtype.coe_mk, mul_one,
                 add_sub_cancel'_right] } }
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
  apply continuous.subtype_mk,
  refine continuous_pi _,
  rintro ⟨i, hi⟩,
  apply continuous_if_const; intro h,
  { exact continuous_induced_dom.comp continuous_fst },
  { cases i with i, trivial,
    refine (continuous_induced_dom.comp 
           $ unit_interval.continuous_symm.comp continuous_fst).mul _,
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
    simp only [inclusion, simplex_category.to_Top'_map_apply,
               fin.mk_zero, simplex_category.coe_to_Top'_map],
    apply finset.sum_eq_zero,
    intros i H,
    exfalso, 
    refine fin.succ_ne_zero i _,
    simp only [finset.mem_filter, finset.mem_univ, true_and] at H, exact H },
  { rw q_map_on_nonzero,
    simp only [inclusion, unit_interval.symm_zero, subtype.val_eq_coe, one_mul, 
               set.Icc.coe_one, simplex_category.to_Top'_map_apply,
               simplex_category.coe_to_Top'_map],
    symmetry, apply finset.sum_eq_single_of_mem,
    { simp only [finset.mem_filter, finset.mem_univ, true_and], ext, refl },
    { intros b hb H,
      exfalso,
      cases b with b hb',
      simp only [finset.mem_filter, finset.mem_univ, true_and] at hb,
      apply H, rw ← hb,
      refl },
    { intro H, apply nat.succ_ne_zero j, apply congr_arg fin.val H } }
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
      from lt_of_le_of_ne (le_sub_comm.mp (le_of_le_of_eq t_le_one (sub_zero 1).symm))
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
           { ext, rw finset.mem_filter,
             simp only [finset.mem_univ, true_and, finset.mem_erase, and_true] },
           { intros k hk,
             rw finset.mem_erase at hk, 
             simp only [ne.def, finset.mem_univ, and_true] at hk,
             rw div_mul_cancel _ denom_nonzero,
             congr,
             symmetry, transitivity, symmetry, exact succ_sigma_of_nonzero n k hk,
             simp only [fin.coe_eq_cast_succ, fin.coe_succ_eq_succ] } },
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
        exact continuous_const.sub (continuous_apply 0) },
      { intros x hx, exact x.property (sub_eq_zero.mp hx).symm }
    }
  }

lemma q_section_is_section (n : ℕ) (σ : topological_simplex (n + 1)) (h : σ.val 0 ≠ 1)
  : function.uncurry (q_map n) (q_section n ⟨σ, h⟩) = σ :=
begin
  dsimp only [function.uncurry],
  ext k,
  by_cases h' : (k = 0),
  { rw h', refl },
  { rw q_map_on_nonzero _ _ _ _ h',
    simp only [q_section, unit_interval.symm, subtype.val_eq_coe, subtype.coe_mk,
               fin.coe_eq_cast_succ, fin.coe_succ_eq_succ, continuous_map.coe_mk],
    rw [subtype.coe_mk, mul_comm, div_mul_cancel _ _],
    { congr, apply succ_sigma_of_nonzero, assumption },
    { intro h'', apply h, symmetry, rw ← sub_eq_zero, exact h'' } }
end

lemma q_section_on_preimage_of_image
  (n : ℕ) (p : I × topological_simplex n) (h : (function.uncurry (q_map n) p).val 0 ≠ 1)
  : q_section n ⟨function.uncurry (q_map n) p, h⟩ = p :=
begin
  cases p with t σ, ext,
  { simp only [q_map, q_section, function.uncurry_apply_pair, eq_self_iff_true, 
               if_true, continuous_map.coe_mk, subtype.coe_eta] },
  { simp only [q_section, function.uncurry_apply_pair, subtype.val_eq_coe,
               fin.coe_eq_cast_succ, fin.coe_succ_eq_succ,
               subtype.coe_mk, continuous_map.coe_mk],
    change (q_map n t σ).val (fin.succ x) / (1 - t) = σ.val x,
    apply div_eq_of_eq_mul (λ h', h.symm (sub_eq_zero.mp h')),
    transitivity, apply q_map_on_nonzero n t σ (fin.succ x) (fin.succ_ne_zero x),
    simp only [q_map, subtype.val_eq_coe, unit_interval.coe_symm_eq, 
               function.uncurry_apply_pair], 
    rw mul_comm, congr,
    exact eq.trans (fin.pred_above_zero (fin.succ_ne_zero x)) (fin.pred_succ _) }
end

lemma q_surj (n : ℕ) : function.surjective (function.uncurry (q_map n)) :=
begin
  intro x,
  by_cases (x.val 0 = 1),
  { existsi ((1 : unit_interval), vertex n 0),
    dsimp only [function.uncurry],
    rw q_map_one_left,
    symmetry,
    rw const_desc,
    apply eq_vertex,
    assumption },
  { exact ⟨q_section n ⟨x, h⟩, q_section_is_section n x h⟩ }
end

lemma q_quot (n : ℕ) : quotient_map (function.uncurry (q_map n)) := 
begin
  apply_with surjection_of_compact_hausdorff_is_quot_map {instances:=ff},
  { apply_with prod.compact_space {instances:=ff},
    apply_instance,
    dsimp only [topological_simplex, simplex_category.to_Top'_obj],
    apply_instance },
  apply_instance,
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
    map_add' := by { intros, cases n; dsimp only [ε_map],
      { apply finsupp.sum_add_index',
        { intro, simp only [zero_smul]},
        { intros, apply add_smul } },
      { simp only [pi.zero_apply, add_zero] } },
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
    intros i j h, simp only [complex_shape.down_rel] at h, subst h,
    cases j; ext σ σ'; 
    simp only [ε_hom, ε_map, linear_map.coe_comp, Module.coe_comp, 
               map_zero, pi.zero_apply, finsupp.coe_zero, function.comp_app,
               finsupp.lsingle_apply, finsupp.sum_apply, finsupp.coe_smul,
               pi.smul_apply, algebra.id.smul_eq_mul, linear_map.coe_mk],
    { rw singular_chain_complex_differential_desc_deg_0,
      rw finsupp.sum_sub_index,
      { symmetry, rw sub_eq_zero, dsimp only [simplex_to_chain],
        rw [finsupp.sum_single_index, finsupp.sum_single_index]; 
        simp only [zero_mul] },
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

lemma cone_construction_hom_naturality (R : Type*) [comm_ring R] {X Y : Top} (x0 : X) (y0 :Y)
  (f : X ⟶ Y)
  (H  : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (H' : continuous_map.homotopy (continuous_map.id Y) (continuous_map.const Y y0)) (i : ℕ)
  (hf : cylinder.map f ≫ H'.to_continuous_map = H.to_continuous_map ≫ f)
  : cone_construction_hom R x0 H i ≫ ((singular_chain_complex R).map f).f (i + 1)
  = ((singular_chain_complex R).map f).f i ≫ cone_construction_hom R y0 H' i :=
begin
  delta singular_chain_complex free_complex_on_sset,
  simp only [cone_construction_hom, simplicial_object.whiskering_obj_map_app,
             alternating_face_map_complex_map_f, Module.free_map, functor.comp_map],
  refine eq.trans (finsupp.lmap_domain_comp R R _ _).symm
          (eq.trans _ (finsupp.lmap_domain_comp R R _ _)),
  apply congr_arg,
  ext σ : 1,
  symmetry, 
  dsimp [Top.to_sSet', cone_construction_lift_simplex],
  rw lift_along_quot_map_comm_square,
  congr' 1,
  rw [category.assoc, ← hf], 
  simp only [functor.map_comp, category.assoc]
end

noncomputable
def cone_construction_complex_hom (R : Type*) [comm_ring R] {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0))
  (i j : ℕ) : ((singular_chain_complex R).obj X).X i ⟶ ((singular_chain_complex R).obj X).X j :=
  if h : i + 1 = j
  then (cone_construction_hom R x0 H i) ≫ eq_to_hom (congr_arg _ h)
  else 0

lemma cone_construction_hom_on_face {X : Top} (x0 : X)
  (H : continuous_map.homotopy (continuous_map.id X) (continuous_map.const X x0)) (i : ℕ)
  (j : fin (i + 2)) (σ : Top.of (topological_simplex (i + 1)) ⟶ X)
  : cone_construction_lift_simplex x0 H i
                                   (simplex_category.to_Top'.map (simplex_category.δ j) ≫ σ)
  = simplex_category.to_Top'.map (simplex_category.δ j.succ)
  ≫ cone_construction_lift_simplex x0 H (i + 1) σ :=
begin
  ext p,
  simp only [Top.comp_app, simplex_category.to_Top'_map_apply],
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
    cases p' with p1 p2, 
    simp only [simplex_category.to_Top'_map_apply, continuous_map.coe_mk,
               function.uncurry_apply_pair],
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
    simp only [continuous_map.coe_mk, function.uncurry_apply_pair],
    rw q_map_one_left, 
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
    simp only [continuous_map.coe_mk, function.uncurry_apply_pair],
    rw q_map_zero_left },
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
  simp only [homotopy.d_next_zero_chain_complex, linear_map.zero_apply,
             homotopy.prev_d_chain_complex, Module.coe_comp, function.comp_app,
             zero_add],
  dsimp only [cone_construction_complex_hom],
  split_ifs, swap, contradiction,
  dsimp [cone_construction_hom],
  rw finsupp.map_domain_single,
  rw singular_chain_complex_differential_desc_deg_0,
  dsimp only [simplex_to_chain],
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
  simp only [homotopy.d_next_succ_chain_complex, Module.coe_comp,
             function.comp_app, homotopy.prev_d_chain_complex],
  dsimp only [cone_construction_complex_hom],
  split_ifs, swap, contradiction,
  symmetry, rw ← eq_sub_iff_add_eq',
  transitivity, exact congr_arg _ finsupp.map_domain_single,
  rw singular_chain_complex_differential_desc,
  rw fin.sum_univ_succ,
  rw sub_eq_add_neg, apply congr_arg2,
  { simp only [simplex_to_chain, fin.coe_zero, pow_zero, finsupp.smul_single,
               int.smul_one_eq_coe, algebra_map.coe_one],
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
    zero' := by { intros i j h, dsimp at h,
                  dsimp only [cone_construction_complex_hom],
                  split_ifs, contradiction, refl }, 
    comm := by {
      intros, ext σ : 2, dsimp only [homological_complex.id],
      -- squeeze_dsimp doesn't work :/
      cases i; dsimp [ε, ε_hom, ε_map], 
      { rw [finsupp.sum_single_index, one_smul],
        apply cone_construction_comm_zero,
        apply zero_smul },
      { rw [add_zero], apply cone_construction_comm_higher_deg }
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

lemma simplex_to_chain_is_basis (R : Type*) [comm_ring R] (n : ℕ) (X : Top)
  (σ : Top.of (topological_simplex n) ⟶ X)
  : @simplex_to_chain n (Top.to_sSet'.obj X) σ R _
  = ((singular_chain_complex_basis R n).get_basis X) ⟨(), σ⟩ :=
begin
  intros, dsimp [functor_basis.get_basis, simplex_to_chain], rw basis.mk_apply,
  symmetry, refine eq.trans finsupp.map_domain_single _,
  congr, apply category.id_comp
end
-- #check basis.quotient
noncomputable
def singular_homology0_basis (R : Type*) [comm_ring R] [nontrivial R] (X : Top)
  : basis (zeroth_homotopy X) R ((singular_homology R 0).obj X) :=
  have hrel : (complex_shape.down ℕ).rel 1 0, by { rw complex_shape.down_rel },
  have hnone : ¬ (complex_shape.down ℕ).rel 0 ((complex_shape.down ℕ).next 0),
  by { dsimp only [complex_shape.next, complex_shape.down_rel], 
       exact nat.succ_ne_zero _ },
  have hnat : homological_complex.d_to ((singular_chain_complex R).obj X) 0
              ≫ (iso.refl (((singular_chain_complex R).obj X).X 0)).hom
            = (homological_complex.X_prev_iso ((singular_chain_complex R).obj X) hrel).hom
              ≫ ((singular_chain_complex R).obj X).d 1 0,
  by { simp only [iso.refl, category.comp_id], 
       exact homological_complex.d_to_eq _ hrel },
  have hs : set.range (quot.mk (path_setoid X).r ∘ λ (x : Σ (i : unit), C(↥(topological_simplex 0), X)), x.snd topological_simplex.point)
          = set.univ,
  by { rw set.eq_univ_iff_forall, intro x, induction x,
       { rw set.range_comp,
         refine set.mem_image_of_mem _ _,
         exact ⟨⟨(), continuous_map.const _ x⟩, rfl⟩ },
       { refl } },
  let f1 := homology_iso_cokernel 0 hnone ((singular_chain_complex R).obj X),
      f2 := cokernel.map_iso (((singular_chain_complex R).obj X).d_to 0)
                            (((singular_chain_complex R).obj X).d 1 0)
                            (((singular_chain_complex R).obj X).X_prev_iso hrel)
                            (iso.refl _) hnat,
      f3 := Module.cokernel_iso_range_quotient (((singular_chain_complex R).obj X).d 1 0),
      L := (f1 ≪≫ f2 ≪≫ f3).to_linear_equiv,
      s : setoid (Σ (i : unit), C(topological_simplex 0, X)) :=
        (path_setoid X).comap (λ x, x.snd topological_simplex.point),
      e : quotient s ≃ zeroth_homotopy X :=
        (setoid.comap_quotient_equiv _ _).trans ((equiv.set_congr hs).trans (equiv.set.univ _)),
      b := (singular_chain_complex_basis R 0).get_basis X in
  have H : linear_map.range (((singular_chain_complex R).obj X).d 1 0)
         = submodule.span R ((λ p : _ × _, b p.fst - b p.snd) '' {p : _ × _ | s.rel p.fst p.snd}),
  begin
    rw linear_map.range_eq_map,
    rw ← free_module_basis_spanning,
    rw linear_map.map_span,
    congr' 1,
    transitivity
      (λ p : X × X, @simplex_to_chain 0 (Top.to_sSet'.obj X) (continuous_map.const _ p.fst) R _
                  - @simplex_to_chain 0 (Top.to_sSet'.obj X) (continuous_map.const _ p.snd) R _)
      '' { p : X × X | joined p.fst p.snd },
    { have joined_eq_range : {p : X × X | joined p.fst p.snd}
                           = (set.range (λ (f : C(I, X)), (f 0, f 1))),
      { ext x, cases x with x y, split,
        { rintro ⟨p⟩, exact ⟨p.to_continuous_map, prod.ext p.source p.target⟩ },
        { rintro ⟨p, h2⟩, simp only [prod.mk.inj_iff] at h2,
          exact ⟨⟨p, h2.left, h2.right⟩⟩ } },
      rw [joined_eq_range, ← set.range_comp, ← set.range_comp],
      rw [← set.image_univ],
      refine eq.trans (congr_arg _ (eq.symm (function.surjective.range_eq _))) _,
      swap, exact (λ g : C(I, X), g.comp one_simplex_homeo_interval.to_continuous_map),
      -- extract this out into a lemma that homeomorphisms α ≃ₜ β induce equivalences C(α, X) ≃ₜ C(β, X) 
      -- possibly deducing this from a general categorical statement
      { intro g, use g.comp one_simplex_homeo_interval.symm.to_continuous_map,
        rw continuous_map.comp_assoc,
        refine (congr_arg _ _).trans (continuous_map.comp_id _),
        rw [homeomorph.to_continuous_map_as_coe, 
            homeomorph.to_continuous_map_as_coe,
            ← homeomorph.coe_trans, homeomorph.self_trans_symm],
        refl },
      rw [← set.range_comp],
      refine congr_arg _ (funext (λ f, _)),
      refine eq.trans (singular_chain_complex_differential_desc_deg_0 R _) _,
      congr,
      refine @fun_like.ext' C(topological_simplex 0, X) _ _ _ _ _ _,
      refine eq.trans (@eq_const_of_unique _ _ topological_simplex.point_unique _) 
                      (congr_arg _ (congr_arg f _)),
      simp only [simplex_category.to_Top'_map, one_simplex_homeo_interval, 
                 subtype.val_eq_coe, subtype.coe_mk, equiv.coe_fn_mk,
                 homeomorph.to_continuous_map_apply, homeomorph.homeomorph_mk_coe, 
                 simplex_category.to_Top'_map_apply],
      refine subtype.ext _, rw [subtype.coe_mk, set.Icc.coe_one],
      unfold_coes,
      dsimp only [simplex_category.δ, simplex_category.hom.mk, fin.succ_above,
                  order_embedding.to_order_hom, order_embedding.of_strict_mono,
                  order_embedding.coe_of_map_le_iff, simplex_category.mk_hom,
                  forget, simplex_category.category_theory.concrete_category,
                  simplex_category.hom.to_order_hom, fin.not_lt_zero,
                  order_embedding.coe_of_map_le_iff, if_false,
                  order_hom.coe_fun_mk],
      refine eq.trans (congr_fun (congr_arg _ $ congr_arg _
                      $ univ_eq_singleton_of_card_one 0 (fintype.card_fin _)) _) _,
      simp only [finset.filter_true_of_mem, finset.mem_singleton, forall_eq, 
                 fin.cast_succ_zero, ite_eq_left_iff, not_lt, fin.le_zero_iff, 
                 fin.one_eq_zero_iff, nat.succ_succ_ne_one, is_empty.forall_iff, 
                 subtype.val_eq_coe, finset.sum_singleton],
      refl },
    { ext, split,
      { rintro ⟨⟨u, v⟩, huv, hsubst⟩, subst hsubst,
        use (⟨(), continuous_map.const _ u⟩, ⟨(), continuous_map.const _ v⟩),
        refine ⟨huv, _⟩, 
        dsimp [b],
        rw [← simplex_to_chain_is_basis, ← simplex_to_chain_is_basis],
        refl },
      { rintro ⟨⟨⟨p1, u⟩, ⟨p2, v⟩⟩, huv, hsubst⟩, 
        subst hsubst, cases p1, cases p2,
        use (u topological_simplex.point, v topological_simplex.point),
        refine ⟨huv, _⟩, 
        dsimp [b], rw [← simplex_to_chain_is_basis, ← simplex_to_chain_is_basis],
        congr; refine @fun_like.ext' C(topological_simplex 0, X) _ _ _ _ _ (eq.symm _);
        convert @eq_const_of_unique _ _ topological_simplex.point_unique _ } }
  end,
  basis.reindex ⟨L.trans (basis.quotient _ _ _ _ b s H).repr⟩ e
  
/-
Move this
-/
lemma setoid.quotient_ker_equiv_range_symm_apply {α : Type*} {β : Type*} (f : α → β)
  (x : α) (y : set.range f) (h : f x = y.val)
  : (setoid.quotient_ker_equiv_range f).symm y = quot.mk (setoid.ker f).r x :=
begin
  dsimp only [setoid.quotient_ker_equiv_range, equiv.of_bijective],
  have h' := setoid.quotient_ker_equiv_range._proof_2 f,
  exact h'.left ((function.surj_inv_eq h'.right y).trans (subtype.ext h.symm))
end

lemma singular_homology0_basis_apply (R : Type*) [comm_ring R] [nontrivial R] (X : Top) (x : X)
  : singular_homology0_basis R X (quot.mk (path_setoid X).r x) 
  = Module.to_homology ⟨simplex_to_chain (continuous_map.const _ x) R,
      by simp only [homological_complex.d_from_eq_zero,
                    chain_complex.next_nat_zero, complex_shape.down_rel,
                    nat.one_ne_zero, not_false_iff, linear_map.ker_zero]⟩ :=
begin
  dsimp only [singular_homology0_basis],
  rw [basis.coe_reindex, function.comp_apply, equiv.symm, equiv.trans,
      ← equiv.to_fun_as_coe],
  unfold_projs,
  rw [function.comp_apply, equiv.trans, equiv.symm, equiv.symm, 
      ← equiv.to_fun_as_coe, ← equiv.to_fun_as_coe],
  unfold_projs,
  rw [function.comp_apply, equiv.set.univ, equiv.set_congr, 
      ← equiv.inv_fun_as_coe, ← equiv.inv_fun_as_coe,
      equiv.subtype_equiv_prop, setoid.comap_quotient_equiv,
      equiv.subtype_equiv, equiv.trans, quotient.congr_right],
  unfold_projs,
  dsimp only [function.comp],
  rw [← equiv.inv_fun_as_coe, quot.congr_right, quot.congr],
  rw @setoid.quotient_ker_equiv_range_symm_apply 
       (Σ (i : unit), C(topological_simplex 0, X)) _ _
       ⟨(), continuous_map.const _ x⟩, swap, refl,
  unfold_projs,
  delta quot.map,
  dsimp only [],
  rw [equiv.refl_symm, equiv.refl_apply, basis.coe_of_repr],
  dsimp only [],
  rw [linear_equiv.trans_symm, linear_equiv.trans_apply,
      ← linear_equiv.inv_fun_eq_symm, ← linear_equiv.inv_fun_eq_symm],
  dsimp only [basis.quotient, linear_equiv.of_linear],
  rw [finsupp.lift_apply, finsupp.sum_single_index, one_smul],
  swap, apply zero_smul,
  dsimp only [quotient.lift, iso.to_linear_equiv],
  rw [iso.trans_inv, iso.trans_inv, comp_apply, comp_apply],
  dsimp only [Module.cokernel_iso_range_quotient, colimit.iso_colimit_cocone,
              Module.cokernel_is_colimit, is_colimit.cocone_point_unique_up_to_iso,
              cocones.forget, functor.map_iso],
  rw [is_colimit.unique_up_to_iso_inv],
  dsimp only [is_colimit.desc_cocone_morphism, cofork.is_colimit.mk],
  rw [← simplex_to_chain_is_basis, submodule.mkq],
  unfold_coes, unfold_projs, dsimp only [],
  rw [submodule.liftq_apply, limits.cokernel.map_iso_inv, 
      ← @comp_apply _ _ _ _ (cokernel (((singular_chain_complex R).obj X).d 1 0))],
  refine (congr_arg _ (congr_arg2 _ (coker_map_spec _ _ _ _ _) rfl)).trans _,
  rw [comp_apply],
  dsimp only [iso.refl, Module.id_apply],
  rw [← comp_apply, Module.homology_iso_cokernel_spec],
  refl
end.

lemma singular_homology0_map_matrix (R : Type*) [comm_ring R] [nontrivial R]
  {X Y : Top} (f : X ⟶ Y) (x : X)
  : (singular_homology R 0).map f (singular_homology0_basis R X (quot.mk (path_setoid X).r x))
  = singular_homology0_basis R Y (quot.mk (path_setoid Y).r (f x)) :=
begin
  rw [singular_homology0_basis_apply, singular_homology0_basis_apply],
  dsimp only [singular_homology, homological_complex.d_from_eq_zero, 
              chain_complex.next_nat_zero, complex_shape.down_rel,
              nat.one_ne_zero, not_false_iff, linear_map.ker_zero],
  delta Module.to_homology, 
  rw ← category_theory.comp_apply,
  simp only [functor.comp_map, homology_functor_map, homology.π_map, 
             Module.coe_comp, function.comp_app],
  refine congr_arg _ _,
  refine eq.trans (Module.cycles_map_to_cycles _ _) _,
  congr,
  refine eq.trans (singular_chain_complex_map _ _ _ _) _,
  delta simplex_to_chain,
  congr
end

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
  congr; apply continuous_map.ext; rintro ⟨x, y⟩; apply prod.ext; refl
end

def inclusion_at_t_nat_trans (t : unit_interval) : category_theory.functor.id Top ⟶ cylinder := {
  app := λ X, ⟨λ x, (t, x), continuous_const.prod_mk continuous_id'⟩
}

lemma inclusion_at_t_nat_trans_on_chain (R : Type*) [comm_ring R]
  (t : unit_interval) (n : ℕ)
  : ((singular_chain_complex R).map
     ((inclusion_at_t_nat_trans t).app 
       ((singular_chain_complex_basis R n).models unit.star))).f n
          ((singular_chain_complex_basis R n).basis_elem unit.star)
  = simplex_to_chain ⟨prod.mk t, by continuity⟩ R :=
begin
  delta singular_chain_complex free_complex_on_sset,
  simp only [functor.comp_map, alternating_face_map_complex_map_f,
             simplicial_object.whiskering_obj_map_app, Module.free_map,
             finsupp.lmap_domain_apply],
  delta singular_chain_complex_basis,
  simp only [simplex_to_chain, finsupp.map_domain_single],
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
       { refine ⟨(λ p, (one_simplex_homeo_interval.to_fun p, topological_simplex.point)), _⟩,
         refine continuous.prod_mk _ continuous_const,
         exact one_simplex_homeo_interval.continuous_to_fun },
       dsimp [simplex_to_chain],
       rw singular_chain_complex_differential_desc_deg_0,
       rw [inclusion_at_t_nat_trans_on_chain, inclusion_at_t_nat_trans_on_chain],
       delta simplex_category.to_Top',
       simp only [],
       rw add_sub_left_comm,
       refine eq.trans (add_zero _).symm _,
       congr,
       { refine funext (λ x, prod.ext (subtype.ext _) (subtype.ext (funext (λ j, _)))),
         simp only [simplex_category.to_Top'_map, set.Icc.coe_zero, 
                    continuous_map.coe_mk, function.comp_app],
         transitivity ((∅ : finset (fin 1)).sum (λ i, x.val i)),
         simp only [subtype.val_eq_coe, finset.sum_empty], refl,
         simp only [continuous_map.coe_mk], congr,
         apply @unique.eq_default _ topological_simplex.point_unique },
       { symmetry, rw sub_eq_zero, congr,
         refine (funext (λ x, prod.ext (subtype.ext _) _)),
         { simp only [simplex_category.to_Top'_map, set.Icc.coe_one, 
                      continuous_map.coe_mk, function.comp_app],
           refine eq.trans x.property.right.symm _, 
           dsimp [one_simplex_homeo_interval],
           congr }, 
         { simp only [continuous_map.coe_mk], apply @unique.eq_default _ topological_simplex.point_unique } } },
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
  apply homotopy.ext, funext p q,
  simp only [singular_homology.chain_homotopy_of_homotopy, pi.zero_apply, zero_add,
             homotopy.trans_hom, pi.add_apply, homotopy.of_eq_hom, add_zero, 
             category.assoc, homotopy.comp_right_hom, homotopy.comp_left_hom],
  by_cases h' : p + 1 = q,
  { rw [← homological_complex.comp_f, ← functor.map_comp, ← h, functor.map_comp,
        homological_complex.comp_f, ← category.assoc, ← functor.comp_map,
        ← (lift_nat_trans_unique (singular_chain_complex_basis R)
                                 (cylinder ⋙ singular_chain_complex R) _ _ _ _).naturality],
    apply category.assoc,
    exact h' },
  { rw ← complex_shape.down_rel _ q p at h',
    rw [homotopy.zero _ _ _ h', homotopy.zero _ _ _ h'],
    simp only [zero_comp, comp_zero] }
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