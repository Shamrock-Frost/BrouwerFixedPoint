import analysis.convex.gauge analysis.normed_space.basic
import topology.category.CompHaus.default
import .general_topology
import analysis.inner_product_space.euclidean_dist
import data.set.function
import .linear_algebra
import analysis.normed_space.hahn_banach.extension
import analysis.normed_space.add_torsor_bases

lemma convex_with_zero_in_int_is_absorbing {E : Type*} [seminormed_add_comm_group E]
  [normed_space ℝ E] (s : set E) (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s)
  : absorbent ℝ s :=
begin
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := hs₂,
  rw metric.is_open_iff at ht1,
  obtain ⟨r, hr1, hr2⟩ := ht1 0 ht3,
  rw absorbent_iff_nonneg_lt, intro x, 
  have H : 0 ≤ r⁻¹ * ∥x∥ := mul_nonneg (inv_nonneg.mpr (le_of_lt hr1)) (norm_nonneg x),
  refine ⟨r⁻¹ * ∥x∥, H, _⟩,
  intros a ha,
  have H' : 0 < ∥a∥ := lt_of_le_of_lt H ha,
  refine ⟨a⁻¹ • x, ht2 (hr2 _), _⟩,
  { rw [mem_ball_zero_iff, norm_smul, mul_comm, norm_inv, mul_inv_lt_iff,
        mul_comm, ← mul_inv_lt_iff, mul_comm], exact ha,
    { exact hr1 },
    { exact H' } },
  { rw ← mul_smul, rw mul_inv_cancel, exact one_smul _ x,
    intro ha', rw [ha', norm_zero] at H', exact lt_irrefl 0 H' }
end

lemma gauge_cont {E : Type*} [seminormed_add_comm_group E] [normed_space ℝ E] (s : set E)
  (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s) : uniform_continuous (gauge s) := 
begin
  have absorbs := convex_with_zero_in_int_is_absorbing s hs₁ hs₂,
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := hs₂,
  rw metric.is_open_iff at ht1,
  obtain ⟨r, hr1, hr2⟩ := ht1 0 ht3,
  have h1 : continuous_at (gauge s) 0,
  { rw metric.continuous_at_iff, simp,
    intros ε hε,
    refine ⟨ε * r, mul_pos hε hr1, _⟩,
    intros x hx,
    rw abs_of_nonneg (gauge_nonneg _),
    refine lt_of_le_of_lt (gauge_mono (absorbent_ball _) (subset_trans hr2 ht2) x) _, 
    { rw norm_zero, exact hr1 },
    { refine gauge_lt_of_mem_smul x ε hε (metric.mem_ball_self hr1) (convex_ball 0 r)
                                  metric.is_open_ball _,
      refine ⟨ε⁻¹ • x, _, _⟩,
      { rw [mem_ball_zero_iff, norm_smul, mul_comm, norm_inv, real.norm_eq_abs,
            abs_eq_self.mpr (le_of_lt hε), mul_inv_lt_iff hε], 
        exact hx },
      { rw ← mul_smul, rw mul_inv_cancel, exact one_smul _ x,
        intro h, rw h at hε, exact lt_irrefl 0 hε } } },
  rw metric.uniform_continuous_iff,
  intros ε hε, rw metric.continuous_at_iff at h1, 
  obtain ⟨δ, hδ, H⟩ := h1 ε hε, simp [abs_of_nonneg, gauge_nonneg] at H,
  refine ⟨δ, hδ, _⟩,
  intros x y hxy,
  rw dist_eq_norm at hxy ⊢,
  apply @lt_of_le_of_lt _ _ _ (max (gauge s (x - y)) (gauge s (y - x))),
  { rw real.norm_eq_abs, rw abs_le, split,
    rw [neg_le, neg_sub], refine le_trans _ (le_max_right _ _),
    swap, refine le_trans _ (le_max_left _ _),
    all_goals 
    { rw sub_le_iff_le_add,
      refine le_trans (le_of_eq _) (gauge_add_le hs₁ absorbs _ _), rw sub_add_cancel } },
  { apply max_lt; apply H, exact hxy, rw norm_sub_rev, exact hxy }
end.

noncomputable
def normalize_by (K E : Type*) [is_R_or_C K] [normed_add_comm_group E] [normed_space K E]
  (f : E → K) := λ x, (f x * (∥x∥⁻¹ : K)) • x

lemma normalize_by_continuous (K E : Type*) [is_R_or_C K] [normed_add_comm_group E]
  [normed_space K E] (f : E → K) (hf1 : continuous f) (hf2 : f 0 = 0)
  : continuous (normalize_by K E f) :=
begin
  suffices : continuous_on (normalize_by K E f) (set.univ \ {0}) 
           ∧ continuous_at (normalize_by K E f) 0,
  { obtain ⟨h1, h2⟩ := this,
    constructor,
    intros U hU,
    rw ← set.compl_eq_univ_diff at h1,
    rw continuous_on_open_iff at h1,
    { specialize h1 U hU,
      by_cases (0 : E) ∈ U,
      { rw continuous_at_def at h2,
        specialize h2 U,
        rw mem_nhds_iff at h2,
        specialize h2 ⟨U, subset_refl U, hU, _⟩,
        { simp [normalize_by], exact h },
        rw mem_nhds_iff at h2,
        obtain ⟨t, ht1, ht2, ht3⟩ := h2,
        convert is_open.union h1 ht2,
        rw [set.inter_union_distrib_right, set.union_eq_self_of_subset_right ht1],
        symmetry, convert set.univ_inter _,
        rw [← set.univ_subset_iff],
        refine subset_trans (subset_of_eq (set.compl_union_self {(0 : E)}).symm) _, 
        apply set.union_subset_union_right, rw set.singleton_subset_iff, exact ht3 },
      { convert h1,
        ext, simp, intros h2 h3, rw h3 at h2,
        simp [normalize_by] at h2,
        exact h h2 } },
    { apply is_open_compl_singleton } },
  split,
  { refine continuous_on.smul _ continuous_on_id,
    refine continuous_on.mul hf1.continuous_on _,
    apply continuous_on.inv₀,
    { exact continuous.continuous_on (is_R_or_C.continuous_of_real.comp continuous_norm) },
    { simp } },
  { rw metric.continuous_at_iff,
    intros ε hε, 
    rw metric.continuous_iff at hf1,
    obtain ⟨δ, hδ, H⟩ := hf1 0 ε hε,
    simp at H, 
    refine ⟨δ, hδ, _⟩,
    simp [normalize_by],
    intros x hx,
    convert H x hx,
    rw hf2, simp,
    by_cases x = 0,
    { rw [h, hf2], simp, },
    { rw [mul_smul, norm_smul], simp [norm_smul_inv_norm h] } }
end

noncomputable
def normalize_by_gauge {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] (s : set E)
  := normalize_by ℝ E (gauge s)

lemma norm_of_normalize_by_gauge {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (x : E) : ∥normalize_by_gauge s x∥ = gauge s x :=
begin
  dsimp [normalize_by_gauge, normalize_by],
  by_cases x = 0,
  { subst h, simp },
  { rw [norm_smul, norm_mul, mul_assoc, norm_inv, norm_norm, inv_mul_cancel],
    { rw [real.norm_eq_abs, abs_eq_self.mpr (gauge_nonneg _)], exact mul_one _ },
    { simp, exact h } }
end

lemma normalize_by_gauge_cont {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s)
  : continuous (normalize_by_gauge s) :=
begin
  apply normalize_by_continuous,
  { exact (gauge_cont s hs₁ hs₂).continuous },
  { exact gauge_zero }
end.

lemma interior_eq_gauge_lt_one {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s) 
  : interior s = { p : E | gauge s p < 1 } :=
begin
  let U := { p : E | gauge s p < 1 },
  have : is_open U := is_open.preimage (gauge_cont s hs₁ hs₂).continuous is_open_Iio,
  refine subset_antisymm _ _,
  { rintros x hx,
    have h1 := convex.interior hs₁,
    refine lt_of_le_of_lt (gauge_mono _ interior_subset x) _,
    { apply convex_with_zero_in_int_is_absorbing,
      { assumption }, { rw interior_interior, assumption } },
    { apply gauge_lt_one_of_mem_of_open,
      { assumption },
      { assumption },
      { exact is_open_interior },
      { assumption } } },
  { apply interior_maximal,
    { refine gauge_lt_one_subset_self hs₁ (interior_subset hs₂)
                                      (convex_with_zero_in_int_is_absorbing s hs₁ hs₂) },
    { assumption } }
end

lemma frontier_eq_gauge_one {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s) 
  : frontier s = { p : E | gauge s p = 1 } :=
begin
  unfold frontier,
  rw interior_eq_gauge_lt_one s hs₁ hs₂,
  ext, simp, split; intro h,
  { refine le_antisymm _ h.right,
    change x ∈ { p : E | gauge s p ≤ 1 },
    refine closure_minimal self_subset_gauge_le_one _ h.left,
    exact is_closed.preimage (gauge_cont s hs₁ hs₂).continuous is_closed_Iic },
  { rw h, simp,
    rw mem_closure_iff,
    intros U hU hxU,
    rw metric.is_open_iff at hU,
    obtain ⟨r, hr, H⟩ := hU x hxU,
    let r' := min r (∥x∥/2),
    have H1 : 0 < ∥x∥, { rw norm_pos_iff, intro hx, rw hx at h, simp at h, exact h },
    have H2 : 0 < 1 - ∥x∥⁻¹ * r',
    { rw [sub_pos, ← div_eq_inv_mul, div_lt_one_iff],
      left, exact ⟨H1, lt_of_le_of_lt (min_le_right _ _) (half_lt_self H1)⟩ },
    have : gauge s x < (1 - ∥x∥⁻¹ * r')⁻¹,
    { rw h, rw lt_inv, simp,
      { refine mul_pos (inv_pos.mpr H1) (lt_min hr (half_pos H1)) },
      { exact zero_lt_one },
      { exact H2 } },
    dsimp [gauge] at this, 
    obtain ⟨r'', ⟨hr1'', hx⟩, hr2''⟩ := exists_lt_of_cInf_lt _ this,
    { refine ⟨r''⁻¹ • x, _, _⟩,
      { refine H _,
        simp, refine lt_of_lt_of_le _ (min_le_left r (∥x∥/2)), change dist (r''⁻¹ • x) x < r',
        rw [dist_eq_norm, norm_sub_rev],
        rw (_ : x - r''⁻¹ • x = (1 - r''⁻¹) • x), swap, rw [sub_smul, one_smul],
        rw [norm_smul, real.norm_eq_abs, abs_eq_self.mpr],
        swap,
        { rw [sub_nonneg], apply inv_le_one,
          rw ← h, apply cInf_le, 
          { existsi (0 : ℝ), simp [lower_bounds], intros a ha _, exact le_of_lt ha },
          { exact ⟨hr1'', hx⟩ } },
        { rw [← inv_inv (∥x∥), mul_inv_lt_iff, sub_lt, lt_inv], exact hr2'',
          exact H2, exact hr1'', rw inv_pos, exact H1 } },
      { rw set.mem_smul_set_iff_inv_smul_mem₀ at hx, assumption,
        exact ne.symm (ne_of_lt hr1'') } },
    { apply absorbent.gauge_set_nonempty,
      apply convex_with_zero_in_int_is_absorbing; assumption } },
end.

lemma gauge_eq_zero_iff {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (hs₁ : absorbent ℝ s) (hs₂ : metric.bounded s) (x : E)
  : gauge s x = 0 ↔ x = 0 :=
begin
  split; intro h,
  { rw ← norm_eq_zero,
    refine le_antisymm (le_of_not_lt _) (norm_nonneg x),
    intro h', refine lt_irrefl (∥x∥) _,
    obtain ⟨B, hB⟩ := metric.bounded.subset_ball hs₂ 0,
    let B' := |B| + 1,
    have hB' : s ⊆ metric.closed_ball 0 B',
    { refine subset_trans hB (metric.closed_ball_subset_closed_ball _),
      refine le_trans (le_abs_self B) (le_add_of_nonneg_right zero_le_one) },
    have h'' : 0 < ∥x∥/B',
    { refine div_pos h' (add_pos_of_nonneg_of_pos (abs_nonneg B) zero_lt_one) },
    rw ← h at h'',
    obtain ⟨r, ⟨hr1, hr2⟩, hr3⟩ := exists_lt_of_cInf_lt (absorbent.gauge_set_nonempty _) h'',
    swap, { assumption },
    rw set.mem_smul_set_iff_inv_smul_mem₀ (ne.symm (ne_of_lt hr1)) at hr2,
    specialize hB' hr2, simp at hB',
    rw [norm_smul, mul_comm, norm_inv, real.norm_eq_abs,
        abs_eq_self.mpr (le_of_lt hr1), mul_inv_le_iff hr1] at hB',
    rw lt_div_iff (add_pos_of_nonneg_of_pos (abs_nonneg B) zero_lt_one) at hr3,
    exact lt_of_le_of_lt hB' hr3 },
  { rw h, simp }
end

noncomputable
def compact_convex_with_zero_in_interior_homeo_to_ball
  {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] (s : set E) (hs₁ : convex ℝ s) (hs₂ : (0 : E) ∈ interior s)
  (hs₃ : is_compact s) : s ≃ₜ metric.closed_ball (0 : E) 1 := 
  have h1 : is_compact (metric.closed_ball (0 : E) 1),
  by { obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := hs₂,
       rw metric.is_open_iff at ht1,
       obtain ⟨r, hr1, hr2⟩ := ht1 0 ht3,
       have H : is_compact (metric.closed_ball (0 : E) (r/2)),
       { apply compact_of_is_closed_subset hs₃ metric.is_closed_ball ,
         refine subset_trans (metric.closed_ball_subset_ball _) (subset_trans hr2 ht2),
         exact half_lt_self hr1 },
       convert is_compact.image H (continuous.const_smul continuous_id (2/r)),
       simp, have h : 0 < r / 2 := half_pos hr1,
       rw smul_closed_ball, simp, congr, rw [abs_eq_self.mpr, ← inv_div, inv_mul_cancel],
       exact ne.symm (ne_of_lt h), exact le_of_lt hr1, exact le_of_lt h },
  have h2 : absorbent ℝ s,
  { apply convex_with_zero_in_int_is_absorbing; assumption },
  have h3 : metric.bounded s, from hs₃.bounded,
  let X := @CompHaus.of s _ (is_compact_iff_compact_space.mp hs₃) _,
      Y := @CompHaus.of _ _ (is_compact_iff_compact_space.mp h1) _ in
begin
  refine Top.homeo_of_iso (CompHaus_to_Top.map_iso (@CompHaus.iso_of_bijective X Y ⟨_, _⟩ ⟨_, _⟩)),
  { refine set.cod_restrict (set.restrict s (normalize_by_gauge s)) _ _,
    intro, simp, rw norm_of_normalize_by_gauge, apply gauge_le_one_of_mem, exact x.property },
  { continuity, apply normalize_by_gauge_cont; assumption },
  { simp, rintros ⟨x, hx⟩ ⟨y, hy⟩ hxy, simp at hxy, simp,
    have h4 : gauge s x = gauge s y,
    { rw [← norm_of_normalize_by_gauge, ← norm_of_normalize_by_gauge, hxy] },
    by_cases x = 0,
    { rw h at ⊢ h4, simp at h4, symmetry' at ⊢ h4, rw ← gauge_eq_zero_iff s; assumption },
    { rw ← gauge_eq_zero_iff s h2 h3 at h,
      have h' : ¬ gauge s y = 0,
      { intro h', rw h' at h4, contradiction },
      have h'' : x ≠ 0, { intro h'', rw h'' at h, simp at h, exact h },
      have h''' : y ≠ 0, { intro h''', rw h''' at h', simp at h', exact h' },
      have H : ∥x∥⁻¹ • x = ∥y∥⁻¹ • y,
      { refine eq.trans (inv_smul_smul₀ h _).symm (eq.trans _ (inv_smul_smul₀ h' _)),
        refine congr_arg2 _ (congr_arg (λ t, t⁻¹) h4) _,
        rw [smul_smul, smul_smul], exact hxy },
      suffices : ∥x∥ = ∥y∥,
      { refine eq.trans (smul_inv_smul₀ _ _).symm
                        (eq.trans (congr_arg2 _ this H) (smul_inv_smul₀ _ _));
        rw [norm_ne_zero_iff]; assumption },
      have H' : x = (∥x∥ * ∥y∥⁻¹) • y,
      { rw ← smul_smul, rw inv_smul_eq_iff₀ at H, exact H, rw norm_ne_zero_iff, assumption },
      rw [H', gauge_smul_of_nonneg] at h4,
      rw ← mul_inv_eq_one₀, rw [smul_eq_mul, mul_left_eq_self₀] at h4, exact h4.resolve_right h',
      { rw norm_ne_zero_iff, assumption },
      { exact mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)) } } },
  { simp, rintros ⟨y, hy⟩,
    by_cases y = 0,
    { refine ⟨⟨0, interior_subset hs₂⟩, _⟩,
      simp [normalize_by, normalize_by_gauge, set.restrict, set.cod_restrict], exact h.symm },
    { have h' := h,
      rw ← gauge_eq_zero_iff s h2 h3 at h',
      refine ⟨⟨∥y∥ • (gauge s y)⁻¹ • y, _⟩, _⟩,
      { have := closure_eq_interior_union_frontier s,
        rw hs₃.is_closed.closure_eq at this,
        rw [interior_eq_gauge_lt_one s hs₁ hs₂, frontier_eq_gauge_one s hs₁ hs₂] at this,
        suffices H : gauge s (∥y∥ • (gauge s y)⁻¹ • y) ≤ 1,
        { exact eq.mpr (congr_arg2 _ (refl _) this) (lt_or_eq_of_le H) },
        rw smul_smul,
        rw gauge_smul_of_nonneg (mul_nonneg (norm_nonneg _) (inv_nonneg.mpr (gauge_nonneg _))),
        swap, apply_instance,
        rw [smul_eq_mul, mul_right_comm, mul_inv_cancel_right₀ h'], 
        exact mem_closed_ball_zero_iff.mp hy },
      { simp [normalize_by, normalize_by_gauge, set.restrict, set.cod_restrict],
        rw gauge_smul_of_nonneg (norm_nonneg _); try { apply_instance },
        rw gauge_smul_of_nonneg (inv_nonneg.mpr (gauge_nonneg _)); try { apply_instance },
        rw [smul_smul, smul_smul],
        convert one_smul ℝ y,
        rw [norm_smul, norm_smul, norm_norm, real.norm_eq_abs,
            abs_eq_self.mpr (inv_nonneg.mpr (gauge_nonneg _)),
            mul_inv, mul_inv, inv_inv, smul_eq_mul, smul_eq_mul,
            inv_mul_cancel h', mul_one, mul_inv_cancel_left₀ (norm_ne_zero_iff.mpr h),
            inv_mul_cancel_right₀ (norm_ne_zero_iff.mpr h), mul_comm, inv_mul_cancel h'] } } }
end.

lemma compact_convex_with_nonempty_interior_homeo_to_ball
  {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] (s : set E) (hs₁ : convex ℝ s) (hs₂ : (interior s).nonempty)
  (hs₃ : is_compact s)
  : ∃ (F : s ≃ₜ metric.closed_ball (0 : E) 1),
    F '' (coe ⁻¹' frontier s) = coe ⁻¹' metric.sphere (0 : E) 1 := 
begin
  obtain ⟨p, hp⟩ := hs₂,
  let s' := (λ x, (-p) + x) '' s,
  have hs₁' : convex ℝ s' := hs₁.translate (- p),
  have hs₂' : (0 : E) ∈ interior s',
  { change (0 : E) ∈ interior (homeomorph.add_left (-p) '' s),
    rw ← homeomorph.image_interior (homeomorph.add_left (- p)) s,
    refine ⟨p, hp, _⟩, simp },
  have hs₃' : is_compact s' := hs₃.image (continuous_const.add continuous_id'),
  let G := compact_convex_with_zero_in_interior_homeo_to_ball s' hs₁' hs₂' hs₃',
  refine ⟨homeomorph.trans (embedding_restricts_to_homeomorph s _ (homeomorph.add_left (-p)).embedding) G, _⟩,
  change (G ∘ embedding_restricts_to_homeomorph s _ (homeomorph.add_left (-p)).embedding)
         '' (coe ⁻¹' frontier s) = coe ⁻¹' metric.sphere (0 : E) 1,
  rw set.image_comp,
  transitivity G '' (coe ⁻¹' frontier s'),
  { congr, 
    ext x, cases x with x hx, 
    simp,
    simp [embedding_restricts_to_homeomorph, homeomorph.of_embedding],
    simp_rw [← sub_eq_neg_add, sub_eq_iff_eq_add, ← and_assoc],
    simp,
    rw (_ : s' = (homeomorph.add_left p ⁻¹' s)), swap, simp [s', homeomorph.add_left],
    rw ← homeomorph.preimage_frontier (homeomorph.add_left p) s,
    rw set.mem_preimage, simp [homeomorph.add_left],
    rw add_comm,
    simp, apply hs₃.is_closed.frontier_subset },
  { ext x, cases x with x hx,
    simp [G, compact_convex_with_zero_in_interior_homeo_to_ball, CompHaus.iso_of_bijective,
          set.restrict, set.cod_restrict],
    split,
    { rintros ⟨y, h1, h2, h3⟩,
      rw [← h3, norm_of_normalize_by_gauge],
      convert h2, symmetry,
      exact congr_arg2 (∈) (refl (-p + y)) (frontier_eq_gauge_one s' hs₁' hs₂') },
    { intro h,
      have H : normalize_by_gauge s' (G.symm ⟨x, hx⟩) = x,
      { transitivity (G (G.symm ⟨x, hx⟩)).val,
        { dsimp [G, compact_convex_with_zero_in_interior_homeo_to_ball,
                 CompHaus.iso_of_bijective], refl },
        { simp } },
      refine ⟨p + (G.inv_fun ⟨x, hx⟩).val, _, _, _⟩,
      { simp,
        obtain ⟨z, hz1, hz2⟩ := ((G.symm) ⟨x, hx⟩).property,
        rw subtype.val_eq_coe at hz2,
        rw ← hz2, simp, exact hz1 },
      { simp, rw frontier_eq_gauge_one s' hs₁' hs₂',
        simp,
        rw ← norm_of_normalize_by_gauge,
        convert h, },
      { simp, exact H } } }
end.

noncomputable
def affine_dim (k : Type*) [division_ring k]
  {E : Type*} [add_comm_group E] [module k E] (s : set E) :=
  module.rank k ((affine_span k s).direction)

-- noncomputable 
-- def succ_affine_dim {E : Type*} [add_comm_group E] [module ℝ E] (s : set E)
--   := ⨆ (ι : {t : set E // t ⊆ s ∧ affine_independent ℝ (coe : t → E)}), cardinal.mk ι.val

/-
we will prove that if C is a compact convex set in E with succ_affine_dim C = n + 1 < ∞ 
then C is homeomorphic to the unit ball in ℝ^n
-/
lemma closed_ball_homeo_of_finite_dim (K : Type*) {V W : Type*} [is_R_or_C K]
  [normed_add_comm_group V] [normed_space K V] [finite_dimensional K V]
  [normed_add_comm_group W] [normed_space K W] [finite_dimensional K W] 
  (H : finite_dimensional.finrank K V = finite_dimensional.finrank K W)
  : nonempty (metric.closed_ball (0 : V) 1 ≃ₜ metric.closed_ball (0 : W) 1) :=
begin
  obtain ⟨F⟩ := finite_dimensional.nonempty_continuous_linear_equiv_of_finrank_eq H,
  let G₁ : metric.closed_ball (0 : V) 1 → metric.closed_ball (0 : W) 1 := λ v, ⟨(∥v.val∥ * ∥F v.val∥⁻¹ : K) • F v.val, _⟩,
  swap,
  { rw [mem_closed_ball_zero_iff, norm_smul, norm_mul, norm_inv,
        is_R_or_C.norm_coe_norm, is_R_or_C.norm_coe_norm, mul_assoc],
    by_cases v.val = 0,
    { rw h, rw [norm_zero, zero_mul], exact zero_le_one },
    { rw [inv_mul_cancel, mul_one], exact mem_closed_ball_zero_iff.mp v.property,
      rw norm_ne_zero_iff, exact (linear_equiv.map_ne_zero_iff F.to_linear_equiv).mpr h } },
  let G₂ : metric.closed_ball (0 : W) 1 → metric.closed_ball (0 : V) 1 := λ v, ⟨(∥v.val∥ * ∥F.symm v.val∥⁻¹ : K) • F.symm v.val, _⟩,
  swap,
  { rw [mem_closed_ball_zero_iff, norm_smul, norm_mul, norm_inv,
        is_R_or_C.norm_coe_norm, is_R_or_C.norm_coe_norm, mul_assoc],
    by_cases v.val = 0,
    { rw h, rw [norm_zero, zero_mul], exact zero_le_one },
    { rw [inv_mul_cancel, mul_one], exact mem_closed_ball_zero_iff.mp v.property,
      rw norm_ne_zero_iff, exact (linear_equiv.map_ne_zero_iff F.symm.to_linear_equiv).mpr h } },
  refine ⟨⟨⟨G₁, G₂, _, _⟩, continuous_subtype_mk _ _, continuous_subtype_mk _ _⟩⟩,
  any_goals
  { rintro ⟨x, hx⟩, simp [G₁, G₂], by_cases x = 0, { rw h, simp },
    rw norm_smul_inv_norm' (norm_nonneg _),
    swap, exact (linear_equiv.map_ne_zero_iff (continuous_linear_equiv.to_linear_equiv _)).mpr h,
    rw [norm_smul, norm_mul, norm_inv, is_R_or_C.norm_coe_norm, is_R_or_C.norm_coe_norm,
        ← is_R_or_C.of_real_inv, mul_inv, mul_inv, inv_inv, ← mul_smul], 
    convert one_smul _ _,
    simp, field_simp, rw mul_right_comm,
    apply div_self,
    refine mul_ne_zero (mul_self_ne_zero.mpr _) _; norm_cast; rw norm_eq_zero,
    exact h, exact (linear_equiv.map_ne_zero_iff (continuous_linear_equiv.to_linear_equiv _)).mpr h },
  { refine continuous.comp (_ : continuous (λ v : V,  ((∥v∥ : K) * ((∥F v∥)⁻¹ : K)) • F v))
                           continuous_subtype_val,
    convert continuous.comp (_ : continuous (λ w : W,  ((∥F.symm w∥ : K) * ((∥w∥)⁻¹ : K)) • w))
                            F.continuous_to_fun,
    { ext, simp },
    { apply normalize_by_continuous,
      { continuity },
      { simp } } },
  { refine continuous.comp (_ : continuous (λ w : W,  ((∥w∥ : K) * ((∥F.symm w∥)⁻¹ : K)) • F.symm w))
                           continuous_subtype_val,
    convert continuous.comp (_ : continuous (λ v : V,  ((∥F v∥ : K) * ((∥v∥)⁻¹ : K)) • v))
                            F.symm.continuous_to_fun,
    { ext, simp, congr, symmetry, exact F.to_linear_equiv.right_inv x },
    { apply normalize_by_continuous,
      { continuity },
      { simp } } }
end.

/-
Cool results that I did not end up needing
-/
lemma hahn_banach_finite_dim {K : Type*} [is_R_or_C K] {V E : Type*} [seminormed_add_comm_group E]
  [normed_space K E] [normed_add_comm_group V] [normed_space K V] [finite_dimensional K V] 
  (p : subspace K E) (f : ↥p →L[K] V) : ∃ (g : E →L[K] V), ∀ (x : ↥p), g x = f x :=
begin
  let d := finite_dimensional.finrank K V,
  let b : basis (fin d) K V := finite_dimensional.fin_basis K V,
  let T := b.equiv_fun.to_continuous_linear_equiv,
  suffices : ∃ (g : E →L[K] (fin d → K)), ∀ (x : ↥p), g x = (T.to_continuous_linear_map.comp f) x,
  { obtain ⟨g, H⟩ := this,
    refine ⟨continuous_linear_map.comp T.symm.to_continuous_linear_map g, _⟩,
    intro x, convert congr_arg T.symm.to_continuous_linear_map (H x),
    symmetry, exact continuous_linear_equiv.symm_apply_apply T (f x) },
  let fi : fin d → ↥p →L[K] K := λ i, continuous_linear_map.comp ((pi.basis_fun K (fin d)).coord i).to_continuous_linear_map
                                                                 (T.to_continuous_linear_map.comp f),
  let gi : fin d → (E →L[K] K) := λ i, classical.some (exists_extension_norm_eq p (fi i)),
  have gi_spec : ∀ (i : fin d), (∀ (x : p), gi i x = fi i x) ∧ (∥gi i∥ = ∥fi i∥)
    := λ i, classical.some_spec (exists_extension_norm_eq p (fi i)),
  replace gi_spec := λ i, and.left (gi_spec i),
  refine ⟨continuous_linear_map.pi gi, _⟩,
  intro x, ext i,
  rw continuous_linear_map.coe_pi',
  dsimp,
  rw gi_spec,
  dsimp [fi],
  rw pi.basis_fun_repr
end.

lemma injective_continuous_linear_map_is_embedding (K : Type*) {V E : Type*} [is_R_or_C K]
  [normed_add_comm_group V] [normed_space K V] [finite_dimensional K V]
  [normed_add_comm_group E] [normed_space K E] 
  (T : V →ₗ[K] E) (hT : function.injective T) : embedding T :=
begin
  suffices : ∃ S : E →L[K] V, function.left_inverse S T,
  { obtain ⟨S, hS⟩ := this,
    exact function.left_inverse.embedding hS (map_continuous S) (map_continuous T) },
  let p := T.range,
  let G : V ≃ₗ[K] p := linear_equiv.of_injective T hT,
  obtain ⟨g, hg⟩ := hahn_banach_finite_dim p G.symm.to_linear_map.to_continuous_linear_map,
  refine ⟨g, _⟩,
  intro, convert hg (G x), symmetry, exact linear_equiv.symm_apply_apply G x
end

lemma convex_spanning_set_has_nonempty_interior {V : Type*}
  [normed_add_comm_group V] [normed_space ℝ V] [finite_dimensional ℝ V]
  (s : set V) (hs₁ : convex ℝ s) (hs₂ : (0 : V) ∈ s) (hs₃ : submodule.span ℝ s = ⊤)
  : (interior s).nonempty :=
begin
  rw hs₁.interior_nonempty_iff_affine_span_eq_top,
  rw eq_top_iff at ⊢ hs₃, rw affine_subspace.le_def, rw ← set_like.coe_subset_coe at hs₃,
  refine subset_trans hs₃ _,
  simp [span_points], intros x hx,
  refine ⟨0, hs₂, x, _, (add_zero x).symm⟩,
  refine submodule.span_mono _ hx,
  intros y hy, refine ⟨y, 0, hy, hs₂, sub_zero y⟩
end

lemma convex_compact_homeo_to_ball {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  (s : set E) (hs₁ : convex ℝ s) (hs₂ : is_compact s) (hs₃ : s.nonempty)
  (n : ℕ) (hs₄ : affine_dim ℝ s = n)
  : nonempty (s ≃ₜ metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1) :=
begin 
  obtain ⟨x0, hx0⟩ := hs₃,
  haveI : finite_dimensional ℝ (affine_span ℝ s).direction,
  { cases n,
    { exact finite_dimensional_of_dim_eq_zero hs₄ },
    { apply finite_dimensional.finite_dimensional_of_finrank_eq_succ, swap, exact n, 
      refine eq.trans _ (cardinal.to_nat_cast (n + 1)), exact congr_arg cardinal.to_nat hs₄ } },
  suffices : nonempty (s ≃ₜ metric.closed_ball (0 : (affine_span ℝ s).direction) 1),
  { obtain ⟨F⟩ := this, refine ⟨F.trans _⟩,
    refine nonempty.some (closed_ball_homeo_of_finite_dim ℝ _),
    rw finrank_euclidean_space_fin,
    dsimp [finite_dimensional.finrank], dsimp [affine_dim] at hs₄,
    rw hs₄, exact cardinal.to_nat_cast n },
  let F : (affine_span ℝ s).direction → E := λ q, x0 +ᵥ q,
  have hF1 : s ⊆ set.range F,
  { refine subset_trans (subset_span_points ℝ s) (subset_of_eq _),
    ext, split,
    { rintros ⟨a, ha, v, hv, H⟩, rw H,
      rw ← direction_affine_span at hv,
      refine ⟨⟨v + (a -ᵥ x0), submodule.add_mem _ hv _⟩, _⟩,
      { rw direction_affine_span,
        apply vsub_mem_vector_span_of_mem_span_points_of_mem_span_points;
        apply mem_span_points; assumption },
      { simp [F], rw [subtype.coe_mk, add_left_comm, ← add_sub_assoc, add_sub_cancel'] } },
    { rintro ⟨a, ha⟩, rw ← ha, simp [F],
      rw [add_comm], apply vadd_mem_span_points_of_mem_span_points_of_mem_vector_span,
      { apply mem_span_points, assumption },
      { rw ← direction_affine_span, exact a.property } } },
  have hF2 : embedding F := (homeomorph.vadd x0).embedding.comp embedding_subtype_coe,
  have hF3 : s = F '' (F ⁻¹' s),
  { symmetry, rw set.image_preimage_eq_iff, exact hF1 },
  let F' : F ⁻¹' s ≃ₜ s, { convert embedding_restricts_to_homeomorph (F⁻¹' s) F hF2 },
  suffices : nonempty (F ⁻¹' s ≃ₜ metric.closed_ball (0 : (affine_span ℝ s).direction) 1),
  { obtain ⟨G⟩ := this, refine ⟨F'.symm.trans G⟩ },
  have hF' : convex ℝ (F ⁻¹' s),
  { intros a b ha hb u v hu hv huv, simp [F],
    have h : (x0 : E) = u • (x0 : E) + v • (x0 : E),
    { rw [← add_smul, huv, one_smul] },
    rw [h, ← add_assoc, add_right_comm (u • x0), add_assoc, ← smul_add, ← smul_add],
    exact hs₁ ha hb hu hv huv },
  refine nonempty_of_exists (compact_convex_with_nonempty_interior_homeo_to_ball _ hF' _ _),
  { apply convex_spanning_set_has_nonempty_interior _ hF',
    { simp [F], assumption },
    { rw eq_top_iff, rintros ⟨x, hx⟩ _,
      suffices : ∀ (y : E) (hy : y ∈ vector_span ℝ s),
               (⟨y, (direction_affine_span ℝ s).substr hy⟩ : (affine_span ℝ s).direction)
               ∈ submodule.span ℝ (F ⁻¹' s),
      { exact this x ((direction_affine_span ℝ s).subst hx) },
      intros y hy, refine submodule.span_induction' _ _ _ _ hy,
      { rintros z ⟨a, b, ha, hb, h⟩, 
        have h1 : a -ᵥ x0 ∈ (affine_span ℝ s).direction,
        { rw direction_affine_span, apply vsub_mem_vector_span; assumption },
        have h2 : b -ᵥ x0 ∈ (affine_span ℝ s).direction,
        { rw direction_affine_span, apply vsub_mem_vector_span; assumption },
        suffices : (⟨_, h1⟩ : (affine_span ℝ s).direction) - (⟨_, h2⟩ : (affine_span ℝ s).direction)
                 ∈ submodule.span ℝ (F ⁻¹' s),
        { convert this, rw ← h, simp },
        refine submodule.sub_mem _ _ _;
        refine submodule.subset_span _;
        simp [F]; assumption },
      { exact submodule.zero_mem _ },
      { intros _ _ _ _ h1 h2, exact submodule.add_mem _ h1 h2 },
      { intros a _ _ h, exact submodule.smul_mem _ a h } } },
  { rw is_compact_iff_compact_space at ⊢ hs₂, haveI := hs₂, exact F'.symm.compact_space }
end.

