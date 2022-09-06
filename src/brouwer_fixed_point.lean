import .homology_of_spheres
import algebra.quadratic_discriminant

lemma connected_to_disconnected_surjection_nogo {α β : Type*}
  [topological_space α] [topological_space β] (h1 : connected_space α) (h2 : ¬ connected_space β)
  : ¬ ∃ (r : C(α, β)), function.surjective r :=
begin
  rintros ⟨r, h⟩,
  have : is_connected (set.range r) := is_connected_range r.continuous_to_fun,
  rw h.range_eq at this,
  refine h2 _,
  exact @connected_space.mk _ _ ⟨this.right⟩ (set.nonempty_iff_univ_nonempty.mpr this.left)
end

lemma ball_to_sphere_retraction_nogo (n : ℕ)
  : ¬ ∃ (r : C(metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1,
               metric.sphere (0 : euclidean_space ℝ (fin n)) 1)),
      ∀ x h, (r ⟨x, metric.sphere_subset_closed_ball h⟩ : euclidean_space ℝ (fin n)) = x :=
begin
  rw not_exists,
  intros r H,
  let i : C(metric.sphere (0 : euclidean_space ℝ (fin n)) 1,
            metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1)
        := ⟨_, continuous_inclusion metric.sphere_subset_closed_ball⟩,
  have : r.comp i = continuous_map.id _,
  { ext : 2, cases a with a ha, exact H a ha },
  by_cases n > 0,
  { let i' : Top.of (metric.sphere (0 : euclidean_space ℝ (fin n)) 1)
          ⟶ Top.of (metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1)
        := i,
    let r' : Top.of (metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1)
          ⟶ Top.of (metric.sphere (0 : euclidean_space ℝ (fin n)) 1)
        := r,
    cases n, { exact lt_irrefl 0 h },
    by_cases n > 0,
    { change i' ≫ r' = 𝟙 (Top.of (metric.sphere (0 : euclidean_space ℝ (fin (n + 1))) 1)) at this,
      replace this := congr_arg (@category_theory.functor.map _ _ _ _ (singular_homology ℤ n) _ _) this,
      simp at this,
      have H : category_theory.limits.is_zero ((singular_homology ℤ n).obj (Top.of (metric.closed_ball (0 : euclidean_space ℝ (fin (n + 1))) 1))),
      { obtain ⟨P⟩ := homology_of_contractible_space ℤ (Top.of (metric.closed_ball (0 : euclidean_space ℝ (fin (n + 1))) 1)) _ n h,
        exact category_theory.limits.is_zero_of_iso_of_zero (category_theory.limits.is_zero_zero _) P.symm,
        exact convex.contractible_space (strict_convex_closed_ball ℝ _ _).convex 
                                        ⟨0, metric.mem_closed_ball_self zero_le_one⟩ },
      refine absurd (category_theory.limits.is_zero_of_iso_of_zero H (category_theory.iso.mk _ _ _ this)) _,
      { exact category_theory.limits.is_zero.eq_of_src H _ _ },
      { obtain ⟨P⟩ := @nth_homology_of_n_sphere ℤ _ _ n h,
        intro H', 
        have H'' := category_theory.limits.is_zero_of_iso_of_zero H' P,
        rw category_theory.limits.is_zero_iff_id_eq_zero at H'', 
        have H''' : (𝟙 (Module.of ℤ ℤ) : ℤ → ℤ) 1 = 0, { rw H'', refl },
        exact @one_ne_zero ℤ _ _ H''' } },
    { simp at h, subst h,
      refine connected_to_disconnected_surjection_nogo _ _ ⟨r, _⟩,
      { rw ← is_connected_iff_connected_space,
        refine convex.is_connected (strict_convex_closed_ball ℝ _ _).convex
                                   ⟨0, metric.mem_closed_ball_self zero_le_one⟩ },
      { let x0 : (metric.sphere (0 : euclidean_space ℝ (fin 1)) 1) := ⟨(λ _, (-1) : fin 1 → ℝ), _⟩,
        swap, { simp [euclidean_space.norm_eq] },
        let x1 : (metric.sphere (0 : euclidean_space ℝ (fin 1)) 1) := ⟨(λ _, 1 : fin 1 → ℝ), _⟩,
        swap, { simp [euclidean_space.norm_eq] },
        let F := two_point_t2_space_homeo_coprod_two_points x0 x1 _ _,
        { intro h, haveI := h,
          have h' : is_connected (set.range F.symm) := is_connected_range F.symm.continuous_to_fun,
          rw [F.symm.range_coe, sum.is_connected_iff] at h',
          cases h', 
          { obtain ⟨t, _, ht⟩ := h',
            have := @set.mem_univ (punit.{1} ⊕ punit.{1}), rw ht at this,
            specialize this (sum.inr ()), cases this with _ h'', simp at h'', exact h'' },
          { obtain ⟨t, _, ht⟩ := h',
            have := @set.mem_univ (punit.{1} ⊕ punit.{1}), rw ht at this,
            specialize this (sum.inl ()), cases this with _ h'', simp at h'', exact h'' } },
        { simp [x0, x1], refine ne.symm _, rw [ne.def, eq_neg_self_iff], exact one_ne_zero },
        { rintro ⟨x, hx⟩, simp [euclidean_space.norm_eq] at hx, simp [x0, x1], 
          refine or.imp _ _ (or.symm hx); intro; ext i; fin_cases i; assumption } },
      { refine @function.right_inverse.surjective _ _ r i _,
        intro x, rw [← continuous_map.comp_apply, this], refl } } },
  { simp at h, subst h, 
    suffices : is_empty ↥(metric.sphere (0 : euclidean_space ℝ (fin 0)) 1),
    { obtain ⟨h⟩ := this, exact h (r ⟨0, metric.mem_closed_ball_self zero_le_one⟩) },
    apply_with metric.sphere_is_empty_of_subsingleton {instances:=ff},
    { dsimp [euclidean_space, pi_Lp], apply_instance },
    { exact zero_ne_one.symm } }
end.

notation `⟪`x`, `y`⟫` := @inner ℝ _ _ x y

noncomputable
def time_to_boundary (n : ℕ) (p q : euclidean_space ℝ (fin n)) : ℝ :=
  (2 * ⟪q - p, q⟫ - real.sqrt (4 * ⟪q - p, q⟫^2 + 4 * ∥p - q∥^2 * (1 - ∥q∥^2))) / (2 * ∥p - q∥^2)

noncomputable
def time_to_boundary_aux (x : { tuple : ℝ × ℝ × ℝ // tuple.snd.fst > 0 ∧ tuple.snd.snd ≤ 1 }) : ℝ :=
  (2 * x.val.fst - real.sqrt (4 * x.val.fst^2 + 4 * x.val.snd.fst^2 * (1 - x.val.snd.snd^2))) / (2 * x.val.snd.fst^2)

noncomputable
def time_to_boundary' (n : ℕ) (pair : { x : metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                                           × metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                                           // x.fst ≠ x.snd })
  := time_to_boundary n pair.val.fst pair.val.snd

noncomputable
def time_to_boundary'_aux (n : ℕ) (pair : { x : metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                                              × metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                                              // x.fst ≠ x.snd })
  : { tuple : ℝ × ℝ × ℝ // tuple.snd.fst > 0 ∧ tuple.snd.snd ≤ 1 } := {
    val := ⟨⟪pair.val.snd.val - pair.val.fst.val, pair.val.snd⟫,
            ∥pair.val.fst.val - pair.val.snd.val∥,
            ∥pair.val.snd.val∥⟩,
    property := by { split; simp, { rw [sub_eq_zero, ← subtype.ext_iff], exact pair.property },
                     { have := pair.val.snd.property, simp at this, exact this } }
  }.

lemma time_to_boundary'_fact (n : ℕ)
  : time_to_boundary' n  = time_to_boundary_aux ∘ time_to_boundary'_aux n :=
begin
  ext x, rcases x with ⟨⟨⟨x1, h1⟩, ⟨x2, h2⟩⟩, h⟩, refl
end.

lemma time_to_boundary'_continuous (n : ℕ) : continuous (time_to_boundary' n) :=
begin
  rw time_to_boundary'_fact,
  refine continuous.comp _ _,
  { refine continuous.div _ _ _, { continuity }, { continuity },
    { rintro ⟨⟨a, b, c⟩, h1, h2⟩, rw mul_ne_zero_iff, simp, exact ne_of_gt h1 } },
  { refine continuous_subtype_mk _ _, 
    refine continuous.prod_mk _ ((continuous_norm.comp _).prod_mk (continuous_norm.comp _)),
    { refine continuous.inner _ _,
      { exact continuous.sub (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val))
                             (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)) },
      { exact continuous_subtype_coe.comp (continuous_snd.comp continuous_subtype_val) } },
    { exact continuous.sub (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val))
                             (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)) },
    { exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val) } }
end.

lemma real.quadratic_eq_zero_iff {a b c : ℝ} (ha : a ≠ 0) (h : discrim a b c ≥ 0) (x : ℝ) :
  a * x * x + b * x + c = 0
  ↔ x = (-b + real.sqrt (discrim a b c)) / (2 * a) ∨ x = (-b - real.sqrt (discrim a b c)) / (2 * a) :=
  quadratic_eq_zero_iff ha (by { rw [← pow_two, real.sq_sqrt h] }) x

lemma real.AM_GM2 (a b : ℝ) : 2 * a * b ≤ a^2 + b^2 :=
  sub_nonneg.mp (eq.subst (sub_sq' a b) (sq_nonneg (a - b))) 

lemma time_to_boundary'_lands_in_sphere (n : ℕ) (pair)
  : time_to_boundary' n pair • pair.val.fst.val + (1 - time_to_boundary' n pair) • pair.val.snd.val
  ∈ metric.sphere (0 : euclidean_space ℝ (fin n)) 1 :=
begin
  simp, generalize h : time_to_boundary' n pair = t,
  rw [norm_eq_sqrt_real_inner, real_inner_add_add_self,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_smul_right,
      real.sqrt_eq_iff_sq_eq _ zero_le_one, one_pow],
  { ring_nf SOP,
    rw [mul_assoc, ← mul_neg, ← mul_add, ← mul_add, mul_assoc, mul_assoc, ← mul_sub],
    symmetry,
    rw [mul_comm t _, mul_comm, pow_two, ← mul_assoc, ← sub_eq_zero, add_sub_assoc],
    rw real.quadratic_eq_zero_iff,
    { right,
      rw ← h, delta time_to_boundary' time_to_boundary discrim,
      congr' 2,
      { rw [neg_sub, mul_comm, inner_sub_left, sub_mul], refl },
      { refine congr_arg _ _,
        rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self, inner_sub_left], 
        rw [← neg_sq, neg_sub, ← sub_mul, mul_pow, mul_comm],
        congr, norm_cast,
        rw [← mul_neg, neg_sub, ← real_inner_self_eq_norm_sq,
            sub_eq_add_neg, add_assoc, mul_comm (2 : ℝ)], refl },
      { rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self,
            sub_eq_add_neg, add_assoc, mul_comm (2 : ℝ)], refl } },
    { refine ne_of_eq_of_ne _ (sq_eq_zero_iff.not.mpr (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (subtype.ext_iff.not.mp pair.property)))),
      rw [← real_inner_self_eq_norm_sq, real_inner_sub_sub_self], ring },
    { delta discrim,
      rw [ge_iff_le, sub_nonneg, sub_sq],
      transitivity (0 : ℝ),
      { rw [← neg_nonneg, ← mul_neg, neg_sub],
        refine mul_nonneg (mul_nonneg zero_le_four _) _,
        { rw [← sub_eq_neg_add, add_sub_left_comm, add_comm, mul_comm, ← real_inner_sub_sub_self,
              real_inner_self_eq_norm_sq],
         apply sq_nonneg },
        { rw [sub_nonneg, real_inner_self_eq_norm_sq, sq_le_one_iff (norm_nonneg _),
              ← mem_closed_ball_zero_iff],
          exact subtype.mem _ } },
      { rw [add_comm, ← add_sub_assoc, sub_nonneg, add_comm], apply real.AM_GM2 } } },
  { ring_nf SOP,
    rw [mul_assoc, ← mul_neg, ← mul_add, ← mul_add, mul_assoc, mul_assoc, ← mul_sub],
    rw [← sub_eq_neg_add, add_sub_left_comm, add_comm _ (_ - _), mul_comm _ (2 : ℝ),
        ← real_inner_sub_sub_self, real_inner_self_eq_norm_sq],
    rw [mul_comm _ (2 : ℝ), ← mul_sub, ← inner_sub_left, add_right_comm,
        ← sub_neg_eq_add, sub_nonneg],
    refine le_trans (neg_le_abs_self _) _,
    rw [← real_inner_smul_left, ← real_inner_smul_left, smul_smul, mul_comm, ← smul_smul],
    refine le_trans (abs_real_inner_le_norm _ _) _,
    rw [norm_smul, real.norm_eq_abs, abs_eq_self.mpr (zero_le_two : (0 : ℝ) ≤ (2 : ℝ))],
    refine le_trans (real.AM_GM2 _ _) (le_of_eq _),
    rw [norm_smul, real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq] }
end.

-- rcases pair with ⟨⟨⟨p, hp⟩, ⟨q, hq⟩⟩, h⟩,
-- rw [subtype.val_eq_coe],
-- simp only [prod.fst, prod.snd, subtype.coe_mk],

lemma time_to_boundary_eq_zero_if_in_boundary (n : ℕ) (p q : euclidean_space ℝ (fin n)) 
  (h1 : p ∈ metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1)
  (h2 : q ∈ metric.sphere (0 : euclidean_space ℝ (fin n)) 1)
  : time_to_boundary n p q = 0 :=
begin
  simp at h1 h2,
  simp only [div_eq_zero_iff, time_to_boundary],
  left,
  rw [h2, one_pow, sub_self, mul_zero, add_zero, real.sqrt_mul, sub_eq_zero], 
  symmetry, congr,
  { rw real.sqrt_eq_iff_sq_eq; norm_cast; apply nat.zero_le },
  { apply real.sqrt_sq,
    rw [inner_sub_left, sub_nonneg, real_inner_self_eq_norm_mul_norm],
    refine le_trans (real_inner_le_norm _ _) _,
    rw h2, simp, exact h1 },
  { norm_cast, exact nat.zero_le 4 }
end

/-
Proof sketch, due to Ivo Vekemans (see https://www.ivovekemans.net/mathematical-art):

I slept.
And slumbering dreamt.
And dreaming, I ambled clockwise around a great circular lake in an infinite desert.
And ambling, caught my sweater on a thorn, and began to unravel.
And unravelling, I saw all the points of the lake.
And observed, the lake began to stir.
And stirring, the surface did not break, remaining contained.
And contained, the visited a violent vortex, but STILL the surface did not break.
And unbroken, the whirring pool... ...subsided, as the last sweater thread unwound.
And unwound in the setting sun I spied again the thorn.
And spying, noticed that no point on the lake was where it began.
And beginning at each point emanated a single ray of light, through the point it was prior perturbation, each ray illuminating a spot on the shore.
And sure that the points perturbed from the bank illuminated those points from whence they came, I tied the ends of my sweater together and HEAVED. And heaved and heaved.
And, so heft, the thread, without breaking or crossing the lake, rewound unto me a complete sweater.
And sweating from the exertion, I woke.
And waking, recalled that one is not zero, snapping the thread.
-/

lemma brouwer_fixed_point_for_sphere (n : ℕ)
  (f : C(metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1,
         metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1))
  : ∃ x : metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1, f x = x :=
begin
  by_contra, rw not_exists at h,
  apply ball_to_sphere_retraction_nogo n,
  let mk_pair : metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
              → { x : metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                    × metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1
                    // x.fst ≠ x.snd } := λ p, ⟨⟨f p, p⟩, h p⟩,
  have mk_pair_cont : continuous mk_pair :=
    continuous_subtype_mk _ (continuous.prod_mk f.continuous_to_fun continuous_id),
  let r :  C(metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1,
             metric.sphere (0 : euclidean_space ℝ (fin n)) 1) :=
    continuous_map.comp ⟨(λ p, ⟨time_to_boundary' n p • p.val.fst.val
                                + (1 - time_to_boundary' n p) • p.val.snd.val,
                                time_to_boundary'_lands_in_sphere n p⟩), _⟩
                        ⟨mk_pair, mk_pair_cont⟩,
  swap,
  { refine continuous_subtype_mk _ (continuous.add _ _);
    refine continuous.smul _ _,
    { exact time_to_boundary'_continuous n },
    { exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val) },
    { exact continuous.sub (continuous_const) (time_to_boundary'_continuous n) },
    { exact continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val) } },
  refine ⟨r, _⟩,
  intros x h,
  simp [r, mk_pair, time_to_boundary'],
  rw time_to_boundary_eq_zero_if_in_boundary n _ _ (subtype.mem _) h,
  simp
end.

theorem brouwer_fixed_point {V : Type*}
  [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]
  : ∀ (s : set V), convex ℝ s → is_compact s → set.nonempty s → 
    ∀ (f : C(s, s)), ∃ x, f x = x :=
begin
  intros s h1 h2 h3,
  have : affine_dim ℝ s < cardinal.aleph_0, 
  { apply @lt_of_le_of_lt _ _ _ (module.rank ℝ V),
    { dsimp [affine_dim],
      rw [← finite_dimensional.finrank_eq_dim, ← finite_dimensional.finrank_eq_dim],
      norm_cast,
      apply submodule.finrank_le },
    { rw ← finite_dimensional.finrank_eq_dim, exact cardinal.nat_lt_aleph_0 _ } },
  rw cardinal.lt_aleph_0 at this, 
  obtain ⟨n, hn⟩ := this,
  obtain ⟨F⟩ := convex_compact_homeo_to_ball s h1 h2 h3 n hn,
  intro f, 
  let g := F.to_continuous_map.comp (f.comp F.symm.to_continuous_map),
  obtain ⟨y, hy⟩ := brouwer_fixed_point_for_sphere n g,
  refine ⟨F.symm y, _⟩,
  rw [← homeomorph.coe_symm_to_equiv, equiv.eq_symm_apply],
  exact hy
end