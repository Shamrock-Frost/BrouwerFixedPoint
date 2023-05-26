import LTE_port.homology
import .barycentric_subdivision .reduced_homology .convex

-- Should rework this so everything is a subset of ℝ^(n+1) and we just intersect
def topological_simplex_boundary (n : ℕ) := topological_simplex n ∩ { p | ∃ i, p i = 0 }

def topological_simplex_boundary_minus_bottom_face (n : ℕ) := 
  topological_simplex_boundary n ∩ { p | 0 < p 0 }

def topological_simplex_boundary_minus_bottom_face_is_open (n : ℕ)
  : is_open (coe ⁻¹' topological_simplex_boundary_minus_bottom_face n
            : set (topological_simplex_boundary n)) :=
begin
  dsimp [is_open, subtype.topological_space], 
  simp_rw is_open_induced_iff',
  simp [topological_simplex_boundary_minus_bottom_face],
  refine ⟨{ p | 0 < p 0 }, _, rfl⟩,
  { change is_open ((λ (p : fin (n + 1) → ℝ), p 0) ⁻¹' (set.Ioi 0)),
    apply is_open.preimage, apply continuous_apply,
    exact is_open_Ioi }
end

def topological_simplex_boundary_minus_top_vertex (n : ℕ) := 
  topological_simplex_boundary n \ {(vertex n 0).val}

lemma topological_simplex_boundary_minus_top_vertex_alt_desc (n : ℕ)
  : topological_simplex_boundary_minus_top_vertex n = topological_simplex_boundary n ∩ { p | p 0 ≠ 1 } :=
begin
  dsimp [topological_simplex_boundary_minus_top_vertex],
  refine set.inter_eq_inter_iff_left.mpr _,
  split,
  { rintros p ⟨h1, h2⟩, simp, intro hp, rw hp at h2, refine h2 _, exact vertex_coord_one n 0 },
  { rintros p ⟨h1, h2⟩, simp, intro hp, refine h2 _, simp, 
    exact congr_arg subtype.val (eq_vertex n 0 ⟨p, h1.left⟩ hp) }
end

def topological_simplex_boundary_minus_top_vertex_is_open (n : ℕ)
  : is_open (coe ⁻¹' topological_simplex_boundary_minus_top_vertex n
            : set (topological_simplex_boundary n)) :=
begin
  rw topological_simplex_boundary_minus_top_vertex_alt_desc,
  dsimp [is_open, subtype.topological_space], rw is_open_induced_iff',
  simp [topological_simplex_boundary_minus_top_vertex],
  refine ⟨{ p | p 0 ≠ 1 }, _, rfl⟩,
  change is_open ((λ (p : fin (n + 1) → ℝ), p 0) ⁻¹' ({ r | r ≠ 1 })),
  apply is_open.preimage, apply continuous_apply,
  exact is_open_ne
end

lemma simplex_minus_bottom_face_and_minus_top_vertex_cover (n : ℕ)
  : topological_simplex_boundary_minus_top_vertex n ∪ topological_simplex_boundary_minus_bottom_face n
  = topological_simplex_boundary n := 
begin
  rw topological_simplex_boundary_minus_top_vertex_alt_desc,
  ext,
  simp [topological_simplex_boundary_minus_bottom_face, topological_simplex_boundary_minus_top_vertex],
  rw ← and_or_distrib_left,
  simp, intro hx, apply not_or_of_imp,
  intro h, rw h, exact zero_lt_one
end

open category_theory

/-
move
-/
noncomputable
def Module.to_relative_homology {R : Type*} [comm_ring R] {ι : Type*} {c : complex_shape ι}
  {C D : homological_complex (Module R) c} (f : C ⟶ D) {i j : ι} (hij : c.rel i j)
  (x : D.X i) (hx : D.d i j x ∈ linear_map.range (f.f j)) : ((limits.cokernel f).homology i) :=
  Module.to_homology ⟨(limits.cokernel.π f).f i x, by {
    rw linear_map.mem_ker,
    rw ← category_theory.comp_apply,
    rw homological_complex.d_from_eq _ hij,
    rw ← category.assoc,
    rw (limits.cokernel.π f).comm i j,
    dsimp,
    convert map_zero _,
    exact Module.chain_complex_cokernel_π_zero_of_in_range f _ hx
  }⟩.


noncomputable
def simplex_to_relative_chain (R : Type*) [comm_ring R] (A X : Top) (f : A ⟶ X) (hf : embedding f)
  (n : ℕ) (σ : C(topological_simplex (n + 1), X))
  (H : ∀ i, set.range (simplex_category.to_Top'.map (@simplex_category.δ n i) ≫ σ) ⊆ set.range f)
  : (singular_homology_of_pair R (n + 1)).obj (arrow.mk f) :=
  Module.to_relative_homology ((singular_chain_complex R).map f)
                              (complex_shape.down_mk (n + 1) n rfl)
                              (simplex_to_chain σ R)
                              (by { change (((singular_chain_complex R).obj X).d (n + 1) n) (finsupp.single σ 1)
                                           ∈ linear_map.range (((singular_chain_complex R).map f).f n),
                                    rw singular_chain_complex_differential_desc,
                                    refine submodule.sum_mem _ _,
                                    intros k _,
                                    rw zsmul_eq_smul_cast R,
                                    refine submodule.smul_mem _ _ _,
                                    specialize H k,
                                    refine ⟨simplex_to_chain (hf.pullback _ H) R, _⟩,
                                    refine eq.trans (singular_chain_complex_map R n _ _) _,
                                    dsimp [simplex_to_chain],
                                    congr' 1,
                                    ext, dsimp, apply embedding.pullback_spec }).

def topological_simplex_boundary_incl_topological_simplex (n : ℕ)
  : Top.of (topological_simplex_boundary n) ⟶ Top.of (topological_simplex n) :=
  ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩

def inclusion_embedding {α : Type*} [topological_space α] {s t : set α} (h : s ⊆ t) 
  : embedding (set.inclusion h) := {
    induced := by { dsimp [subtype.topological_space], rw induced_compose, congr },
    inj := set.inclusion_injective h
  }

noncomputable
def topological_simplex_relative_homology_generator (R : Type*) [comm_ring R] (n : ℕ)
  : (singular_homology_of_pair R (n + 1)).obj (arrow.mk (topological_simplex_boundary_incl_topological_simplex (n + 1))) :=
  simplex_to_relative_chain R _ _ (topological_simplex_boundary_incl_topological_simplex (n + 1))
                            (inclusion_embedding _) n
                            (𝟙 (Top.of (topological_simplex (n + 1))))
                            (by { intro i,
                                  transitivity set.range (simplex_category.to_Top'.map (simplex_category.δ i)),
                                  { refine subset_of_eq _, congr },
                                  { dsimp [topological_simplex_boundary_incl_topological_simplex],
                                    rintros x ⟨y, h⟩, subst h,
                                    rw set.range_inclusion,
                                    simp [topological_simplex_boundary],
                                    existsi i,
                                    simp [simplex_category.to_Top'_map],
                                    apply finset.sum_eq_zero,
                                    intros j hj, exfalso,
                                    simp [simplex_category.δ, simplex_category.hom.mk] at hj,
                                    exact fin.succ_above_ne _ _ hj } }).

def topological_simplex_boundary_minus_interior_of_bottom_face (n : ℕ)
  := topological_simplex_boundary n ∩ { p | ∃ i, i ≠ 0 ∧ p i = 0 }

lemma topological_simplex_boundary_minus_bottom_face_alt_desc (n : ℕ)
  : topological_simplex_boundary_minus_bottom_face n 
  = topological_simplex_boundary_minus_interior_of_bottom_face n ∩ { p | 0 < p 0 } :=
begin
  simp [topological_simplex_boundary_minus_bottom_face,
        topological_simplex_boundary_minus_interior_of_bottom_face],
  symmetry, rw [set.inter_comm, ← set.inter_assoc],
  symmetry, rw set.inter_comm, symmetry, rw set.inter_eq_left_iff_subset,
  rintros x ⟨h1, _, i, hi⟩,
  refine ⟨i, _, hi⟩,
  intro h, rw h at hi,
  refine ne_of_lt _ hi.symm,
  exact h1
end

lemma topological_simplex_boundary_minus_bottom_face_subset_minus_interior_of_bottom_face (n : ℕ)
  : topological_simplex_boundary_minus_bottom_face n
  ⊆ topological_simplex_boundary_minus_interior_of_bottom_face n :=
  by { rw topological_simplex_boundary_minus_bottom_face_alt_desc, simp }

lemma topological_simplex_boundary_minus_interior_of_bottom_face_star_convex (n : ℕ)
  : star_convex ℝ (vertex n 0).val
                (topological_simplex_boundary_minus_interior_of_bottom_face n) :=
begin
  dsimp [topological_simplex_boundary],
  rintros y ⟨⟨hy, _⟩, ⟨i, hi1, hi2⟩⟩ s t hs ht hst, 
  refine ⟨⟨_, _⟩, _⟩,
  { apply convex_std_simplex ℝ (fin (n + 1)), exact (vertex n 0).property,
    all_goals { assumption } },
  all_goals { existsi i, simp },
  swap, refine ⟨hi1, _⟩,
  all_goals
  { convert add_zero _,
    { rw hi2, simp },
    { symmetry, convert mul_zero _,
      refine vertex_coord_zero _ _ _ _,
      intro h, subst h, exact hi1 rfl } }
end

lemma topological_simplex_boundary_minus_bottom_face_star_convex (n : ℕ)
  : star_convex ℝ (vertex n 0).val
                (topological_simplex_boundary_minus_bottom_face n) :=
begin
  intros y hy s t hs ht hst,
  have := topological_simplex_boundary_minus_interior_of_bottom_face_star_convex n
            (topological_simplex_boundary_minus_bottom_face_subset_minus_interior_of_bottom_face n hy)
            hs ht hst,
  rw topological_simplex_boundary_minus_bottom_face_alt_desc,
  refine ⟨this, _⟩,
  simp,
  convert convex_Ioi (0 : ℝ) zero_lt_one hy.right hs ht hst,
  exact vertex_coord_one n 0
end

def topological_simplex_boundary_minus_bottom_face_minus_top_vertex (n : ℕ) :=
  topological_simplex_boundary_minus_bottom_face n ∩ topological_simplex_boundary_minus_top_vertex n

def topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex
  (n : ℕ) := topological_simplex_boundary_minus_interior_of_bottom_face n
             ∩ topological_simplex_boundary_minus_top_vertex n

def continuous_map.is_homotopy_equiv {X : Type*} {Y : Type*}
  [topological_space X] [topological_space Y] (f : C(X, Y)) : Prop :=
  ∃ (g : C(Y, X)), (g.comp f).homotopic (continuous_map.id X) 
                 ∧ (f.comp g).homotopic (continuous_map.id Y)

lemma homotopy_equiv_induces_quasi_iso {R : Type*} [comm_ring R] {X Y : Top} (f : X ⟶ Y)
  (hf : f.is_homotopy_equiv) : quasi_iso ((singular_chain_complex R).map f) :=
begin
  obtain ⟨g, ⟨H⟩, ⟨H'⟩⟩ := hf,
  constructor,
  intro n,
  constructor,
  existsi (singular_homology R n).map g,
  split;
  refine eq.trans _ ((singular_homology R n).map_id _);
  rw ← functor.comp_map;
  refine eq.trans ((singular_homology R n).map_comp _ _).symm _;
  apply singular_homology.homotopy_invariant;
  assumption
end

structure deformation_retraction {A X : Top} (i : A ⟶ X) (hi : embedding i) :=
(H : C(I × X, X))
(map_zero_left' : ∀ x, H (0, x) = x)
(map_one_left' : ∀ x, ∃ a : A, i a = H (1, x))
(is_retract : ∀ a, i a = H (1, i a))

universe u
def deformation_retraction.is_homotopy_equivalence {A X : Top.{u}} (i : A ⟶ X) (hi : embedding i)
  (H : deformation_retraction i hi) : i.is_homotopy_equiv :=
begin
  let r := hi.pullback { to_fun := λ x, H.H (1, x) } (set.range_subset_iff.mpr H.map_one_left'),
  existsi r,
  split,
  { suffices : r.comp i = continuous_map.id A, { rw this },
    ext a, 
    refine hi.inj _,
    dsimp [r, continuous_map.comp],
    refine eq.trans (hi.pullback_spec _ _ (i a)) _,
    exact (H.is_retract a).symm },
  { symmetry,
    dsimp [continuous_map.homotopic],
    refine ⟨⟨H.H, H.map_zero_left', _⟩⟩,
    intro x,
    symmetry, exact hi.pullback_spec _ _ x }
end

def is_homotopy_equivalence_two_out_of_three_1 {X Y Z : Top} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z)
  (Hf : f.is_homotopy_equiv) (Hh : h.is_homotopy_equiv) (Hcomp : g.comp f = h)
  : g.is_homotopy_equiv :=
begin
  obtain ⟨f', Hf1, Hf2⟩ := Hf,
  obtain ⟨h', Hh1, Hh2⟩ := Hh, 
  refine ⟨f.comp h', _, _⟩,
  { rw continuous_map.comp_assoc,
    suffices : (h'.comp g).homotopic f',
    { transitivity f.comp f',
      { refine continuous_map.homotopic.hcomp this (continuous_map.homotopic.refl f) },
      { assumption } },
    suffices : (h'.comp (g.comp f)).homotopic (continuous_map.id X),
    { rw ← continuous_map.comp_assoc at this,
      have := continuous_map.homotopic.hcomp (continuous_map.homotopic.refl f') this,
      rw continuous_map.comp_assoc at this,
      refine continuous_map.homotopic.trans _ (this.trans _),
      { symmetry, exact Hf2.hcomp (continuous_map.homotopic.refl (h'.comp g)) },
      { rw continuous_map.id_comp } },
    rw Hcomp, assumption },
  { transitivity h.comp h',
    { rw ← continuous_map.comp_assoc,
      refine continuous_map.homotopic.hcomp (continuous_map.homotopic.refl h') _,
      convert (nonempty.intro (continuous_map.homotopy.refl h)) },
    { assumption } }
end

def is_homotopy_equivalence_two_out_of_three_2 {X Y Z : Type*}
  [topological_space X] [topological_space Y] [topological_space Z]
  (f : C(X, Y)) (g : C(Y, Z)) (Hf : f.is_homotopy_equiv) (Hg : g.is_homotopy_equiv)
  : (g.comp f).is_homotopy_equiv :=
begin
  obtain ⟨f', Hf1, Hf2⟩ := Hf,
  obtain ⟨g', Hg1, Hg2⟩ := Hg, 
  refine ⟨f'.comp g', _, _⟩,
  { rw [continuous_map.comp_assoc, ← continuous_map.comp_assoc g'],
    transitivity f'.comp ((continuous_map.id Y).comp f),
    { exact continuous_map.homotopic.hcomp
              (continuous_map.homotopic.hcomp (continuous_map.homotopic.refl f) Hg1)
              (continuous_map.homotopic.refl f') },
    { rw continuous_map.id_comp, exact Hf1 } },
  { rw [continuous_map.comp_assoc, ← continuous_map.comp_assoc f],
    transitivity g.comp ((continuous_map.id Y).comp g'),
    { exact continuous_map.homotopic.hcomp
              (continuous_map.homotopic.hcomp (continuous_map.homotopic.refl g') Hf2)
              (continuous_map.homotopic.refl g) },
    { rw continuous_map.id_comp, exact Hg2 } }
end

lemma half_mem_unit_interval : (1 : ℝ)/2 ∈ unit_interval
  := unit_interval.div_mem zero_le_one zero_le_two one_le_two

noncomputable
def star_convex.deformation_retraction {E : Type*} [add_comm_group E] [module ℝ E]
  [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
  {s t : set E} (h : s ⊆ t) {x : E} (hs : star_convex ℝ x s) (ht : star_convex ℝ x t)
  -- we should be able to give a better condition than this..
  (r : C(t, unit_interval))
  (hr1 : ∀ y (hy : y ∈ t), (r ⟨y, hy⟩).val • x + ((1 : ℝ) - (r ⟨y, hy⟩).val) • y ∈ s)
  (hr2 : ∀ y (hy : y ∈ t) (u : ℝ), 0 ≤ u → u < (r ⟨y, hy⟩).val → u • x + ((1 : ℝ) - u) • y ∉ s)
  : @deformation_retraction (Top.of s) (Top.of t) ⟨_, continuous_inclusion h⟩ (inclusion_embedding h)
  := {
    H := {
      to_fun := λ p, ⟨(r p.2 * p.1).val • x + ((1 : ℝ) - r p.2 * p.1) • p.2.val,
                      ht p.snd.property (unit_interval.nonneg (r p.2 * p.1))
                                        (unit_interval.one_minus_nonneg (r p.2 * p.1)) (by simp)⟩,
      continuous_to_fun := by {
        continuity,
        -- no has_continuous_mul instance for unit_interval :/
        refine continuous_induced_rng.mpr _,
        convert (_ : continuous (λ x : I × t, (r.to_fun x.snd).val * x.fst.val)),
        continuity,
        exact r.continuous_to_fun
      }
    },
    map_zero_left' := by { intro, simp },
    map_one_left' := by { rintro ⟨y, hy⟩, simp, exact ⟨⟨_, hr1 y hy⟩, rfl⟩, },
    is_retract := by {
      rintro ⟨y, hy⟩, simp,
      suffices : r ⟨y, h hy⟩ = 0,
      { rw this, simp,  },
      symmetry, apply eq_of_le_of_not_lt unit_interval.nonneg',
      intro h',
      refine hr2 y (h hy) 0 (le_refl 0) h' _,
      convert hy, simp,
    }
  }.

noncomputable
def deformation_retraction.restrict {A B X Y : Top}
  (i : A ⟶ X) (j : B ⟶ Y) (k : X ⟶ Y) (ℓ : A ⟶ B)
  (hi : embedding i) (hj : embedding j) (hk : embedding k) (hℓ : embedding ℓ)
  (hcomm : k ∘ i = j ∘ ℓ)
  (H : deformation_retraction k hk)
  (h1 : ∀ t b, H.H (t, j b) ∈ set.range j)
  (h2 : ∀ b, H.H (1, j b) ∈ set.range (k ∘ i)) 
  : deformation_retraction ℓ hℓ := {
    H := hj.pullback (cylinder.map j ≫ H.H)
                     (set.range_subset_iff.mpr (by { rintro ⟨t, b⟩, exact h1 t b })),
    map_zero_left' := λ x, hj.inj (eq.trans (hj.pullback_spec _ _ _) (H.map_zero_left' (j x))),
    map_one_left' := by { 
      intro b,
      obtain ⟨x, hx⟩ := H.map_one_left' (j b), specialize h2 b, rw ← hx at h2,
      obtain ⟨a, ha⟩ := h2, rw hx at ha, rw hcomm at ha,
      existsi a, apply hj.inj, 
      refine eq.trans ha (eq.symm _),
      exact hj.pullback_spec _ _ _
    },
    is_retract := by {
      intro a, apply hj.inj, 
      symmetry,
      refine eq.trans (hj.pullback_spec _ _ _) (eq.symm _),
      change (j ∘ ℓ) a = H.H (1, (j ∘ ℓ) a),
      rw ← hcomm, dsimp,
      apply H.is_retract
    }
  }

noncomputable
def deformation_retraction.restrict' {X : Type*} [topological_space X]
  {s1 s2 s3 s4 : set X}
  (h12 : s1 ⊆ s2) (h13 : s1 ⊆ s3) (h24 : s2 ⊆ s4) (h34 : s3 ⊆ s4)
  (H : @deformation_retraction (Top.of s3) (Top.of s4) ⟨_, continuous_inclusion h34⟩
                               (inclusion_embedding h34))
  (h1 : ∀ t b (hb : b ∈ s2), (H.H (t, ⟨b, h24 hb⟩)).val ∈ s2)
  (h2 : ∀ b (hb : b ∈ s2), (H.H (1, ⟨b, h24 hb⟩)).val ∈ s1) 
  : @deformation_retraction (Top.of s1) (Top.of s2) ⟨_, continuous_inclusion h12⟩
                            (inclusion_embedding h12) :=
  @deformation_retraction.restrict (Top.of s1) (Top.of s2) (Top.of s3) (Top.of s4)
                                   ⟨_, continuous_inclusion h13⟩
                                   ⟨_, continuous_inclusion h24⟩
                                   ⟨_, continuous_inclusion h34⟩
                                   ⟨_, continuous_inclusion h12⟩
                                   (inclusion_embedding _) (inclusion_embedding _)
                                   (inclusion_embedding _) (inclusion_embedding _)
                                   (by { ext, refl }) H
                                   (by { rintros t ⟨b, hb⟩, simp, apply h1 })
                                   (by { rintros ⟨b, hb⟩, simp, apply h2 }).

noncomputable
def star_convex.deformation_retraction_minus_center {E : Type*} [add_comm_group E] [module ℝ E]
  [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
  {s t : set E} (h : s ⊆ t) {x : E} (hs : star_convex ℝ x s) (ht : star_convex ℝ x t)
  -- we should be able to give a better condition than this..
  (r : C(t, unit_interval))
  (hr1 : ∀ y (hy : y ∈ t), (r ⟨y, hy⟩).val • x + ((1 : ℝ) - (r ⟨y, hy⟩).val) • y ∈ s)
  (hr2 : ∀ y (hy : y ∈ t) (u : ℝ), 0 ≤ u → u < (r ⟨y, hy⟩).val → u • x + ((1 : ℝ) - u) • y ∉ s)
  (hr3 : ∀ y (hy : y ∈ t), y ≠ x → (r ⟨y, hy⟩).val < 1)
  : @deformation_retraction (Top.of (s \ {x} : set E)) (Top.of (t \ {x} : set E))
                            ⟨_, continuous_inclusion (set.diff_subset_diff_left h)⟩
                            (inclusion_embedding (set.diff_subset_diff_left h)) :=
  have h' : ∀ b (hb : b ∈ t \ {x}) (u : ℝ), u ≤ (r ⟨b, hb.left⟩).val → u • x + ((1 : ℝ) - u) • b ≠ x,
  by { intros b hb u hu, 
       simp,
       refine ne_of_ne_of_eq _ (one_smul ℝ x),
       rw [add_comm, ne.def, ← eq_sub_iff_add_eq, ← sub_smul],
       rw smul_right_inj,
       { exact hb.right, },
       { rw [ne.def, sub_eq_zero],
         apply ne.symm, apply ne_of_lt, refine lt_of_le_of_lt hu _,
         apply hr3, exact hb.right } },
  deformation_retraction.restrict' (set.diff_subset_diff_left h) (set.diff_subset s {x})
                                   (set.diff_subset t {x}) h
                                   (star_convex.deformation_retraction h hs ht r hr1 hr2)
                                   (by { intros u b hb,
                                         simp [star_convex.deformation_retraction],
                                         refine ⟨_, h' b hb _ unit_interval.mul_le_left⟩,
                                         refine ht hb.left _ _ _,
                                         { apply mul_nonneg; apply unit_interval.nonneg },
                                         { refine unit_interval.one_minus_nonneg ⟨_, unit_interval.mul_mem _ _⟩,
                                           exact (r _).property, exact u.property },
                                         { apply add_sub_cancel'_right } })   
                                   (by { intros b hb,
                                         simp [star_convex.deformation_retraction],
                                         refine ⟨hr1 b hb.left, _⟩,
                                         exact h' b hb _ (le_refl _) }).

lemma star_convex.inclusion_is_htpy_equiv {E : Type*} [add_comm_group E] [module ℝ E]
  [topological_space E] [has_continuous_add E] [has_continuous_smul ℝ E]
  {c s t : set E} (h1 : c ⊆ s) (h2 : s ⊆ t) {x : E}
  (hc : star_convex ℝ x c) (hs : star_convex ℝ x s) (ht : star_convex ℝ x t)
  -- we should be able to give a better condition than this..
  (r : C(t, unit_interval))
  (hr1 : ∀ y (hy : y ∈ t), (r ⟨y, hy⟩).val • x + ((1 : ℝ) - (r ⟨y, hy⟩).val) • y ∈ c)
  (hr2 : ∀ y (hy : y ∈ t) (u : ℝ), 0 ≤ u → u < (r ⟨y, hy⟩).val → u • x + ((1 : ℝ) - u) • y ∉ c)
  (hr3 : ∀ y (hy : y ∈ t), y ≠ x → (r ⟨y, hy⟩).val < 1)
  : continuous_map.is_homotopy_equiv
      ⟨_, continuous_inclusion (set.diff_subset_diff_left h2 : s \ {x} ⊆ t \ {x})⟩ :=
begin
  let H1 := star_convex.deformation_retraction_minus_center h1 hc hs
                                                            (r.comp ⟨_, continuous_inclusion h2⟩)
                                                            (λ y hy, hr1 y (h2 hy))
                                                            (λ y hy, hr2 y (h2 hy))
                                                            (λ y hy, hr3 y (h2 hy)),
  let H2 := star_convex.deformation_retraction_minus_center (subset_trans h1 h2) hc ht r
                                                            hr1 hr2 hr3,

  have h1 := H1.is_homotopy_equivalence _ _,
  have h2 := H2.is_homotopy_equivalence _ _,
  refine is_homotopy_equivalence_two_out_of_three_1 _ _ _ h1 h2 _,
  { ext, refl }
end

def topological_simplex_minus_bottom_half (n : ℕ) := topological_simplex n ∩ { p | 0.5 ≤ p 0 }

lemma topological_simplex_boundary_minus_bottom_half_star_convex (n : ℕ)
  : star_convex ℝ (vertex n 0).val (topological_simplex_minus_bottom_half n) :=
begin
  refine star_convex.inter ((convex_std_simplex ℝ _).star_convex (vertex n 0).property) _,
  intros x hx s t hs ht hst,
  dsimp at hx,
  simp,
  have := vertex_coord_one n 0,
  dsimp [coe_fn, simplex_category.to_Top'_obj.has_coe_to_fun] at this,
  rw this, 
  have := convex_Ici (1/2 : ℝ),
  convert @this 1 (x 0) _ _ s t hs ht hst,
  swap 6, apply_instance, swap 6, apply_instance,
  simp, refl, refl, 
  exact @half_le_self ℝ _ _ zero_le_one, 
  exact hx
end

-- something about if two embeddings have the same image a deformation retraction of one gives onto the other
def deformation_retraction.transport {A B X : Top} (i : A ⟶ X) (j : B ⟶ X)
  (hi : embedding i) (hj : embedding j)
  (H : deformation_retraction i hi) (hij : set.range i = set.range j)
  : deformation_retraction j hj := {
    H := H.H,
    map_zero_left' := H.map_zero_left',
    map_one_left' := λ x, @eq.subst _ (λ s, H.H (1, x) ∈ s) _ _ hij
                                    (set.mem_range.mpr (H.map_one_left' x)),
    is_retract := by { intro b, have : j b ∈ set.range j := set.mem_range_self b,
                       rw ← hij at this, obtain ⟨a, ha⟩ := this, rw ← ha, exact H.is_retract a }
  }

def topological_simplex_bottom_face (n : ℕ) := topological_simplex n ∩ { p | p 0 = 0 }

def topological_simplex_minus_top_vertex (n : ℕ) := 
  topological_simplex n \ { (vertex n 0).val }

lemma topological_simplex_minus_top_vertex_alt_desc (n : ℕ)
  : topological_simplex_minus_top_vertex n = topological_simplex n ∩ { p | p 0 ≠ 1 } :=
begin
  dsimp [topological_simplex_minus_top_vertex],
  refine set.inter_eq_inter_iff_left.mpr _,
  split,
  { rintros p ⟨h1, h2⟩, simp, intro hp, rw hp at h2, refine h2 _, exact vertex_coord_one n 0 },
  { rintros p ⟨h1, h2⟩, simp, intro hp, refine h2 _, simp, 
    exact congr_arg subtype.val (eq_vertex n 0 ⟨p, h1⟩ hp) }
end

lemma bottom_face_contained_in_boundary_minus_top (n : ℕ)
  : topological_simplex_bottom_face n ⊆ topological_simplex_boundary_minus_top_vertex n :=
begin
  rw topological_simplex_boundary_minus_top_vertex_alt_desc,
  simp [topological_simplex_bottom_face, topological_simplex_boundary_minus_top_vertex,
        topological_simplex_boundary],
  refine ⟨subset_trans (set.inter_subset_right _ _) (λ p hp, ⟨0, hp⟩),
          subset_trans (set.inter_subset_right _ _) (λ p hp hp', zero_ne_one (hp.symm.trans hp'))⟩
end

lemma boundary_minus_top_contained_in_simplex_minus_top (n : ℕ)
  : topological_simplex_boundary_minus_top_vertex n ⊆ topological_simplex_minus_top_vertex n :=
  set.inter_subset_inter_left _ (set.inter_subset_left _ _)

noncomputable
def simplex_minus_top_vertex_deformation_retract_onto_bottom_face (n : ℕ)
  : @deformation_retraction (Top.of (topological_simplex_bottom_face n))
                            (Top.of (topological_simplex_minus_top_vertex n))
                            ⟨_, continuous_inclusion (subset_trans (bottom_face_contained_in_boundary_minus_top n)
                                                                   (boundary_minus_top_contained_in_simplex_minus_top n))⟩ 
                            (inclusion_embedding (subset_trans (bottom_face_contained_in_boundary_minus_top n)
                                                               (boundary_minus_top_contained_in_simplex_minus_top n))) :=
begin
  refine { H := ⟨λ p, ⟨(λ i, (if i = 0
                             then 1 - p.fst
                             else (1 + p.snd.val 0 * (p.fst - 1)) / (1 - p.snd.val 0)) * p.snd.val i),
                      _⟩, _⟩, map_zero_left' := _, map_one_left' := _, is_retract := _ },
  { have := p.snd.property, simp_rw topological_simplex_minus_top_vertex_alt_desc at this,
    simp_rw topological_simplex_minus_top_vertex_alt_desc,
    refine ⟨⟨_, _⟩, _⟩,
    { intro i, dsimp, split_ifs; apply mul_nonneg,
      apply unit_interval.one_minus_nonneg,
      swap, apply div_nonneg, 
      rw [mul_sub, add_sub_left_comm, add_comm, sub_add, ← mul_sub, sub_nonneg],
      apply mul_le_one, rw ← sub_nonneg,
      swap, apply unit_interval.one_minus_nonneg,
      swap, apply sub_le_self, apply unit_interval.nonneg _,
      any_goals { exact p.snd.property.left.left _ },
      all_goals { rw sub_nonneg, exact topological_simplex.coord_le_one n 0 ⟨p.snd.val, p.snd.property.left⟩ } },
    { refine eq.trans (fin.sum_univ_succ _)
                      (eq.trans _ (eq.trans (fin.sum_univ_succ _).symm p.snd.property.left.right)),
      simp, rw [add_comm, ← eq_sub_iff_add_eq],
      rw [sub_mul, ← sub_add, one_mul, add_sub_cancel'],
      transitivity finset.univ.sum (λ x, ((1 + p.snd.val 0 * (p.fst.val - 1)) / (1 - p.snd.val 0) * p.snd.val (fin.succ x))),
      { congr, ext, refine ite_eq_right_iff.mpr _, 
        intro h, exfalso, exact fin.succ_ne_zero _ h },
      { rw ← finset.mul_sum,
        have H : finset.univ.sum (λ x, p.snd.val (fin.succ x)) = 1 - p.snd.val 0,
        { rw eq_sub_iff_add_eq, 
          exact eq.trans (add_comm _ _) (eq.trans (fin.sum_univ_succ _).symm p.snd.property.left.right) },
        rw H, refine eq.trans (div_mul_cancel _ _) _,
        { rw sub_ne_zero, exact this.right.symm },
        { rw [← subtype.val_eq_coe, H, mul_sub, add_sub_left_comm, add_comm, mul_one, mul_comm], refl } } },
    { simp, refine ne_of_lt _, 
      -- use mul_lt_one_of_nonneg_of_lt_one_left
      have h : p.snd.val 0 < 1 := lt_of_le_of_ne _ this.right, swap,
      { exact topological_simplex.coord_le_one n 0 ⟨p.snd.val, p.snd.property.left⟩ },
      apply @lt_of_le_of_lt _ _ _ (p.snd.val 0),
      { refine @unit_interval.mul_le_right (unit_interval.symm p.fst) ⟨_, p.snd.property.left.left _, _⟩,
        exact le_of_lt h },
      { exact h } } },
  { continuity, apply continuous.if_const,
    { exact continuous.fst' (continuous_subtype_val.comp unit_interval.continuous_symm) },
    { refine continuous.comp (_ : continuous (λ p : ℝ × set.Iio (1 : ℝ), (1 + p.2.val * (p.1 - 1))/(1 - p.2.val)))
                             (_ : continuous (λ p : I × topological_simplex_minus_top_vertex n,
                                                  (p.fst.val, (⟨p.snd.val 0, _⟩ : set.Iio (1 : ℝ))))),
      { have := p.snd.property, simp_rw topological_simplex_minus_top_vertex_alt_desc at this,
        refine lt_of_le_of_ne _ this.right,
        exact topological_simplex.coord_le_one n 0 ⟨p.snd.val, p.snd.property.left⟩ },
      { apply continuous.div, 
        { continuity },
        { continuity },
        { intro x, rw sub_ne_zero, exact ne.symm (ne_of_lt x.snd.property) } },
      { continuity, exact (continuous_apply 0).comp (continuous_subtype_val.comp continuous_snd) } },
    { exact (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd) } },
  { intro p, have := p.property, simp_rw topological_simplex_minus_top_vertex_alt_desc at this,
    ext i, dsimp, split_ifs,
    { simp },
    { simp, rw [← sub_eq_add_neg, div_self, one_mul],
      rw sub_ne_zero, exact this.right.symm } },
  { intro p, 
    refine ⟨⟨(λ i, if i = 0 then 0 else (1 - p.val 0)⁻¹ * p.val i), _⟩, _⟩,
    { refine ⟨⟨_, _⟩, _⟩,
      { intro i, dsimp, split_ifs, refl, apply mul_nonneg, 
        { rw [inv_nonneg, sub_nonneg],
          exact topological_simplex.coord_le_one n 0 ⟨p.val, p.property.left⟩ },
        { exact p.property.left.left i } },
      { refine eq.trans (fin.sum_univ_succ _) _, simp,
        transitivity finset.univ.sum (λ x, (1 - p.val 0)⁻¹ * p.val (fin.succ x)),
        { congr, ext, refine ite_eq_right_iff.mpr _, intro h, exfalso, exact fin.succ_ne_zero _ h },
        { rw ← finset.mul_sum, rw inv_mul_eq_one₀, 
          { rw sub_eq_iff_eq_add,
            refine eq.trans (eq.trans p.property.left.right.symm (fin.sum_univ_succ _)) _,
            exact add_comm _ _ },
          { have := p.property, simp_rw topological_simplex_minus_top_vertex_alt_desc at this,
            rw sub_ne_zero, exact this.right.symm } } },
      { refine ite_eq_left_iff.mpr _, intro h, exfalso, exact h rfl } },
    { apply subtype.eq, simp } },
  { intro p, apply subtype.eq, simp, ext i, dsimp, split_ifs,
    { rw h, exact p.property.right },
    { have := p.property.right, dsimp at this, rw this, simp } }
end.

noncomputable
def simplex_boundary_minus_top_vertex_deformation_retract_onto_bottom_face (n : ℕ) :=
  deformation_retraction.restrict'
    (bottom_face_contained_in_boundary_minus_top n) (refl _)
    (set.inter_subset_inter_left _ (set.inter_subset_left _ _))
    (subset_trans (bottom_face_contained_in_boundary_minus_top n)
                  (boundary_minus_top_contained_in_simplex_minus_top n))
    (simplex_minus_top_vertex_deformation_retract_onto_bottom_face n)
    (by { intros,
          refine ⟨⟨((simplex_minus_top_vertex_deformation_retract_onto_bottom_face n).H _).property.left, _⟩,
                  ((simplex_minus_top_vertex_deformation_retract_onto_bottom_face n).H _).property.right⟩,
          obtain ⟨i, hi⟩ := hb.left.right,
          refine ⟨i, _⟩,
          dsimp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face],
          rw hi, exact mul_zero _ })
    (by { intros,
          refine ⟨((simplex_minus_top_vertex_deformation_retract_onto_bottom_face n).H _).property.left, _⟩,
          simp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face] })

def topological_simplex_bottom_face_boundary (n : ℕ) :=
  topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex n ∩ { p | p 0 = 0 }

noncomputable
def topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex_deformation_retract_onto_bottom_face_boundary (n : ℕ) 
  : @deformation_retraction (Top.of (topological_simplex_bottom_face_boundary n))
                            (Top.of (topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex n))
                            ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩ 
                            (inclusion_embedding (set.inter_subset_left _ _)) :=
begin
  apply deformation_retraction.restrict' _
    (set.inter_subset_inter_left _ (subset_trans (set.inter_subset_left _ _)
                                                   (subset_trans (set.inter_subset_left _ _)
                                                                 (set.inter_subset_left _ _))))
    (subset_trans (subset_of_eq (set.inter_assoc _ _ _).symm)
                  (set.inter_subset_inter_left _ (subset_trans (set.inter_subset_right _ _)
                                                               (set.inter_subset_left _ _)))) _
    (simplex_minus_top_vertex_deformation_retract_onto_bottom_face n),
  { rintros t b ⟨⟨⟨h1, _⟩, i, h2, h3⟩, _, h4⟩, dsimp at h4,
    -- tfw no dedup goal
    refine ⟨⟨⟨_, i, _⟩, i, h2, _⟩, ⟨_, i, _⟩, _⟩,
    any_goals
    { rw subtype.val_eq_coe, refine set.inter_subset_left _ _ (subtype.mem _) },
    swap 4,
    { simp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face],
      intro h, dsimp at h, replace h := h.trans subtype.val_eq_coe.symm,
      have : (vertex n 0).val 0 = 1 := vertex_coord_one n 0,
      rw ← h at this,
      refine ne_of_lt _ this,
      simp, rw mul_comm, apply mul_lt_one_of_nonneg_of_lt_one_left,
      { exact h1.left 0 },
      { refine lt_of_le_of_ne (topological_simplex.coord_le_one n 0 ⟨b, h1⟩) _,
        intro h', refine h4 _,
        exact congr_arg subtype.val (eq_vertex n 0 ⟨b, h1⟩ h') },
      { exact unit_interval.one_minus_le_one _ } },
    all_goals
    { dsimp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face],
      rw h3, exact mul_zero _ } },
  { rintros b ⟨⟨⟨h1, _⟩, i, h2, h3⟩, _, h4⟩, dsimp at h4,
    refine ⟨⟨⟨⟨_, i, _⟩, i, h2, _⟩, ⟨_, i, _⟩, _⟩, _⟩,
    any_goals
    { rw subtype.val_eq_coe, refine set.inter_subset_left _ _ (subtype.mem _) },
    any_goals
    { dsimp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face],
      rw h3, exact mul_zero _ },
    { simp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face],
      have : (vertex n 0).val 0 = 1 := vertex_coord_one n 0,
      intro h, replace h := h.trans subtype.val_eq_coe.symm, rw ← h at this,
      simp at this, exact this },
    { simp [simplex_minus_top_vertex_deformation_retract_onto_bottom_face] } }
end.

def include_simplex_as_bottom_face (n : ℕ)
  : C(topological_simplex n, topological_simplex_boundary_minus_top_vertex (n + 1)) :=
begin
  refine {
    to_fun := λ p, ⟨fin.cons 0 p.val, _⟩,
    continuous_to_fun := _
  },
  { rw topological_simplex_boundary_minus_top_vertex_alt_desc,
    refine ⟨⟨_, ⟨0, rfl⟩⟩, zero_ne_one⟩,
    dsimp [topological_simplex, simplex_category.to_Top'_obj, std_simplex], 
    split,
    { rintro ⟨x, hx⟩, cases x; simp [fin.cons, fin.cases, fin.induction], apply p.property.left },
    { refine eq.trans (fin.sum_univ_succ _) _,
      refine eq.trans (zero_add _) _,
      refine eq.trans _ p.property.right,
      congr,
      ext, cases x with x hx,
      refl } },
  { continuity, change continuous ((λ f, @fin.cons (n + 1) (λ _, ℝ) 0 f i) ∘ subtype.val), 
    continuity, cases i with i hi, cases i; simp [fin.cons, fin.cases, fin.induction]; continuity },
end.

lemma include_simplex_as_bottom_face_is_embedding (n : ℕ)
  : embedding (include_simplex_as_bottom_face n) :=
  embedding_of_embedding_compose (include_simplex_as_bottom_face n).continuous_to_fun
                                 (continuous_inclusion (subset_trans (set.inter_subset_left _ _)
                                                                     (set.inter_subset_left _ _)))
                                 (by { apply closed_embedding.to_embedding,
                                       apply closed_embedding_of_continuous_injective_closed,
                                       { exact (continuous_inclusion _).comp (include_simplex_as_bottom_face n).continuous_to_fun },
                                       { rintros ⟨a, _⟩ ⟨b, _⟩ h, apply subtype.eq,
                                         replace h := congr_arg subtype.val h,
                                         dsimp [include_simplex_as_bottom_face] at h,
                                         ext i, convert congr_fun h i.succ; simp },
                                       { intros C hC,
                                         apply is_compact.is_closed,
                                         refine is_compact.image _ ((continuous_inclusion _).comp (include_simplex_as_bottom_face n).continuous_to_fun),
                                         apply_with is_closed.is_compact {instances:=ff},
                                         { change compact_space (std_simplex ℝ (fin (n + 1))),
                                           apply_instance },
                                         { exact hC } } }).

noncomputable
def include_simplex_boundary_as_bottom_face (n : ℕ)
  : C(topological_simplex_boundary n,
      topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex (n + 1)) :=
begin
  refine {
    to_fun := set.cod_restrict (subtype.val ∘ 
                                 ((include_simplex_as_bottom_face n).comp
                                 ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩)) _ _,
    continuous_to_fun := _
  },
  { rintro ⟨x, hx, i, hi⟩, dsimp,
    refine ⟨⟨⟨_, fin.succ i, _⟩, fin.succ i, fin.succ_ne_zero i, _⟩, ⟨_, fin.succ i, _⟩, _⟩,
    any_goals { exact set.inter_subset_left _ _ (set.inter_subset_left _ _ (subtype.mem _)) },
    swap 4,
    { simp [include_simplex_as_bottom_face],
      intro h, replace h := h.trans subtype.val_eq_coe.symm,
      have : (vertex (n+1) 0).val 0 = 1 := vertex_coord_one (n+1) 0, rw ← h at this,
      exact @zero_ne_one ℝ _ _ this },
    all_goals { simp [include_simplex_as_bottom_face], exact hi } },
  { apply continuous.cod_restrict,
    exact continuous_subtype_val.comp (continuous_map.continuous_to_fun _) },
end.

lemma include_simplex_boundary_as_bottom_face_is_embedding (n : ℕ)
  : embedding (include_simplex_boundary_as_bottom_face n) :=
  embedding_of_embedding_compose (include_simplex_boundary_as_bottom_face n).continuous_to_fun
                                 (continuous_inclusion (set.inter_subset_right _ _))
                                 (by { refine eq.mp _ (embedding.comp (include_simplex_as_bottom_face_is_embedding n)
                                                                      (inclusion_embedding (set.inter_subset_left _ _
                                                                                           : topological_simplex_boundary n ⊆ topological_simplex n))),
                                       refine congr_arg _ _,
                                       ext, cases x, refl }).

def preim_of_subset_homeo_subset {α : Type*} [topological_space α] {S T : set α} (h : S ⊆ T)
  : (coe ⁻¹' S : set T) ≃ₜ S := {
    to_fun := λ p, ⟨p.val, p.property⟩,
    inv_fun := λ p, ⟨⟨p.val, h p.property⟩, p.property⟩,
    left_inv := λ p, subtype.eq (subtype.eq rfl),
    right_inv := λ p, subtype.eq rfl
  }.

lemma boundary_inclusion_mono_on_chains {R : Type*} [comm_ring R] (k : ℕ)
  : mono ((singular_chain_complex R).map (topological_simplex_boundary_incl_topological_simplex k)) :=
begin
  apply_with homological_complex.mono_of_eval {instances:=ff}, 
  intro i, refine (Module.mono_iff_injective _).mpr _,
  apply singular_chain_complex_map_inj,
  apply set.inclusion_injective
end  

noncomputable
def homology_rel_boundary_iso_homology_of_boundary {R : Type*} [comm_ring R] [nontrivial R] (n k : ℕ) (hk : k > 0)
  : (singular_homology R k).obj (Top.of (topological_simplex_boundary (n + 1)))
  ≅ (singular_homology_of_pair R k).obj (arrow.mk (topological_simplex_boundary_incl_topological_simplex n)) := 
begin
/-
  Hₖ(topological_simplex_boundary (n + 1))
  ⟶ Hₖ(topological_simplex_boundary (n + 1), topological_simplex_boundary_minus_bottom_face (n + 1))
-/

  let f1 := (singular_homology_of_base_to_of_pair R k).app
              (arrow.mk (⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩
                        : Top.of (topological_simplex_boundary_minus_bottom_face (n + 1)) 
                        ⟶ Top.of (topological_simplex_boundary (n+1)))),

  have h1 : is_iso f1,
  { apply contractible_subspace_homology_of_pair_map_is_iso,
    { exact set.inclusion_injective _ },
    { have : topological_simplex_boundary_minus_bottom_face (n + 1) ⊆ topological_simplex_boundary (n + 1)
           := set.inter_subset_left _ _,
      dsimp,
      refine star_convex.contractible_space (topological_simplex_boundary_minus_bottom_face_star_convex (n+1)) _,
      refine ⟨(vertex (n + 1) 0).val, ⟨(vertex (n + 1) 0).property, _⟩, _⟩,
      { exact ⟨(1 : fin (n + 2)), vertex_coord_zero (n + 1) 0 (1 : fin (n + 2)) fin.zero_ne_one⟩ },
      { dsimp, convert zero_lt_one, exact vertex_coord_one n 0, apply_instance } },
    { assumption } },

/-
  Hₖ(topological_simplex_boundary_minus_top_vertex (n + 1), topological_simplex_boundary_minus_bottom_face (n + 1) ∩ topological_simplex_boundary_minus_top_vertex (n + 1))
  ⟶ Hₖ(topological_simplex_boundary (n + 1), topological_simplex_boundary_minus_bottom_face (n + 1))
-/

  obtain ⟨h2⟩ := excision R (coe ⁻¹' topological_simplex_boundary_minus_top_vertex (n + 1)
                            : set (topological_simplex_boundary (n + 1)))
                           (coe ⁻¹' topological_simplex_boundary_minus_bottom_face (n + 1)
                            : set (topological_simplex_boundary (n + 1)))
                           (topological_simplex_boundary_minus_top_vertex_is_open (n + 1))
                           (topological_simplex_boundary_minus_bottom_face_is_open (n + 1))
                           _,
  swap,
  { rw [← set.preimage_union, eq_top_iff],
    refine set.image_subset_iff.mp _,
    simp only [set.image_univ, subtype.range_coe_subtype, set.top_eq_univ, set.set_of_mem_eq],
    rw simplex_minus_bottom_face_and_minus_top_vertex_cover },
  let i1 : (coe ⁻¹' topological_simplex_boundary_minus_top_vertex (n + 1)
         ∩ coe ⁻¹' topological_simplex_boundary_minus_bottom_face (n + 1)
         : set (topological_simplex_boundary (n + 1)))
         ≃ₜ (topological_simplex_boundary_minus_top_vertex (n + 1) 
         ∩ topological_simplex_boundary_minus_bottom_face (n + 1)
         : set (fin (n + 2) → ℝ)),
  { refine ⟨⟨(λ p, ⟨p.val.val, p.property.left, p.property.right⟩),
            (λ p, ⟨⟨p.val, p.property.left.left⟩, p.property.left, p.property.right⟩),
            _, _⟩, _, _⟩,
    { intro, simp },
    { intro, simp },
    { refine continuous_subtype_mk _ (continuous_subtype_val.comp continuous_subtype_val) },
    { refine continuous_subtype_mk _ (continuous_subtype_mk _ continuous_subtype_val) } },
  let i2 := @preim_of_subset_homeo_subset _ _ (topological_simplex_boundary_minus_top_vertex (n + 1))
                                              (topological_simplex_boundary (n + 1))
                                              (set.inter_subset_left _ _),
  let i3 := @preim_of_subset_homeo_subset _ _ (topological_simplex_boundary_minus_bottom_face (n + 1))
                                              (topological_simplex_boundary (n + 1))
                                              (set.inter_subset_left _ _),
  let e1 : Top.of (topological_simplex_boundary_minus_top_vertex (n + 1)
                   ∩ topological_simplex_boundary_minus_bottom_face (n + 1)
                   : set (fin (n + 2) → ℝ))
           ⟶ Top.of (topological_simplex_boundary_minus_top_vertex (n + 1)) :=
    ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩,
  let e2 : Top.of (topological_simplex_boundary_minus_bottom_face (n + 1))
           ⟶ Top.of (topological_simplex_boundary (n + 1)) :=
    ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩,
  let i4 := @category_theory.arrow.iso_mk _ _
              (arrow.mk (excision_inner_map
                          (coe ⁻¹' topological_simplex_boundary_minus_top_vertex (n + 1))
                          (coe ⁻¹' topological_simplex_boundary_minus_bottom_face (n + 1))))
              (arrow.mk e1) (Top.iso_of_homeo i1) (Top.iso_of_homeo i2) _,
  swap, { ext p, cases p, refl },
  let i5 := @category_theory.arrow.iso_mk _ _
              (arrow.mk (excision_outer_map
                          (coe ⁻¹' topological_simplex_boundary_minus_top_vertex (n + 1))
                          (coe ⁻¹' topological_simplex_boundary_minus_bottom_face (n + 1))))
              (arrow.mk e2) (Top.iso_of_homeo i3) (iso.refl _) _,
  swap, { ext p, cases p, refl },
  let i6 := (singular_homology_of_pair R k).map_iso i4,
  let i7 := (singular_homology_of_pair R k).map_iso i5,

/-
  Hₖ(topological_simplex_boundary_minus_top_vertex (n + 1), topological_simplex_boundary_minus_bottom_face (n + 1) ∩ topological_simplex_boundary_minus_top_vertex (n + 1)) 
  ⟶ Hₖ(topological_simplex_boundary_minus_top_vertex (n + 1), topological_simplex_boundary_minus_interior_of_bottom_face (n + 1) ∩ topological_simplex_boundary_minus_top_vertex (n + 1))
  ^^ iso because coker of quasi isos is iso & homotopy invariance
-/

  let g1 := 𝟙 ((singular_chain_complex R).obj (Top.of (topological_simplex_boundary_minus_top_vertex (n + 1)))),
  have h_aux1 : quasi_iso g1 := quasi_iso_of_iso _,
  -- let s1 := topological_simplex_boundary_minus_bottom_face (n + 1) \ {(vertex (n + 1) 0).val},
  let s1 := topological_simplex_boundary_minus_top_vertex (n + 1)
            ∩ topological_simplex_boundary_minus_bottom_face (n + 1),
  have s1_spec : s1 = topological_simplex_boundary_minus_bottom_face (n + 1) \ {(vertex (n + 1) 0).val},
  { dsimp [s1, topological_simplex_boundary_minus_top_vertex, topological_simplex_boundary_minus_bottom_face], 
    rw [set.diff_eq, set.diff_eq, set.inter_assoc, set.inter_left_comm, set.inter_comm,
        ← set.inter_assoc, set.inter_self] },
  -- let s2 := topological_simplex_boundary_minus_interior_of_bottom_face (n + 1) \ {(vertex (n + 1) 0).val},
  let s2 := topological_simplex_boundary_minus_top_vertex (n + 1)
            ∩ topological_simplex_boundary_minus_interior_of_bottom_face (n + 1),
  have s2_spec : s2 = topological_simplex_boundary_minus_interior_of_bottom_face (n + 1) \ {(vertex (n + 1) 0).val},
  { dsimp [s2, topological_simplex_boundary_minus_top_vertex, topological_simplex_boundary_minus_interior_of_bottom_face], 
    rw [set.diff_eq, set.diff_eq, set.inter_assoc, set.inter_left_comm, set.inter_comm,
        ← set.inter_assoc, set.inter_self, set.inter_right_comm] },
  let g2 : Top.of s1 ⟶ Top.of s2 := 
    ⟨set.inclusion (set.inter_subset_inter_right _
                    (topological_simplex_boundary_minus_bottom_face_subset_minus_interior_of_bottom_face (n + 1))),
     embedding_subtype_coe.to_inducing.continuous_iff.mpr (by continuity)⟩,
  have h_aux2 : (quasi_iso ((singular_chain_complex R).map g2)),
  { apply homotopy_equiv_induces_quasi_iso,
    convert star_convex.inclusion_is_htpy_equiv
              (set.inter_subset_left _ (topological_simplex_minus_bottom_half (n + 1)))
              (topological_simplex_boundary_minus_bottom_face_subset_minus_interior_of_bottom_face (n + 1))
              (star_convex.inter (topological_simplex_boundary_minus_bottom_face_star_convex (n + 1))
                                 (topological_simplex_boundary_minus_bottom_half_star_convex (n + 1)))
              (topological_simplex_boundary_minus_bottom_face_star_convex (n + 1))
              (topological_simplex_boundary_minus_interior_of_bottom_face_star_convex (n + 1))
              ⟨(λ p, ⟨if p.val 0 < 1/2 then 1 - 1 / (2 * (1 - p.val 0)) else 0, _⟩), _⟩ _ _ _,
    swap 5, dsimp [g2], congr,
    any_goals { dsimp [s1, s2, Top.of], congr' 1 },
    { exact eq.trans (eq_true_intro (continuous_inclusion _))
                     (eq_true_intro (continuous_subtype_coe.comp (continuous_inclusion _))).symm },
    { split_ifs,
      { refine ⟨_, _⟩; simp,
        { rw ← mul_inv, apply inv_le_one,
          refine le_of_eq_of_le (inv_mul_cancel_of_invertible (2 : ℝ)).symm _,
          apply decidable.mul_le_mul_of_nonneg_right,
          { rw inv_eq_one_div,
            refine le_of_eq_of_le (sub_half 1).symm _,
            rw sub_le_sub_iff_left, exact le_of_lt h },
          { exact zero_le_two } },
        { exact topological_simplex.coord_le_one (n + 1) 0 ⟨p.val, p.property.left.left⟩, } },
      { exact unit_interval.zero_mem } },
    { refine continuous_subtype_mk _ _,
      refine continuous.comp (_ : continuous (λ p : fin (n + 2) → ℝ, ite (p 0 < 1 / 2) (1 - 1 / (2 * (1 - p 0))) 0))
                             continuous_subtype_coe,
      suffices : continuous (λ t : ℝ, ite (t < 1 / 2) (1 - 1 / (2 * (1 - t))) 0),
      { exact this.comp (continuous_apply (0 : fin (n + 2))) },
      refine continuous_subtype_is_closed_cover (λ (b : bool) (t : ℝ), (b ∧ t ≤ 0.5) ∨ (¬ b ∧ 0.5 ≤ t)) _ _ _ _,
      { apply locally_finite_of_finite },
      { simp, split,
        { exact @is_closed_Ici _ _ _ _ (2⁻¹ : ℝ) }, { exact @is_closed_Iic _ _ _ _ (2⁻¹ : ℝ) } },
      { intro x, simp, apply le_total },
      { simp, split,
        { have : continuous (λ x : ℝ, (0 : ℝ)) := continuous_const,
          refine continuous.congr (this.comp continuous_subtype_val) _,
          rintro ⟨x, hx⟩, simp at hx ⊢, symmetry, rw ite_eq_right_iff, 
          intro hx', exfalso, exact not_le_of_lt hx' hx },
        { have H : (λ (t : ℝ), tt ∧ t ≤ 1 / 2 ∨ ¬tt ∧ 1 / 2 ≤ t) = set.Iic (1 / 2),
          { ext, simp, refl },
          convert (_ : continuous (λ (x : set.Iic (1/2 : ℝ)), 1 - (1 - x.val)⁻¹ * (2 : ℝ)⁻¹)),
          swap 3, apply function.hfunext, congr,
          any_goals { exact H },
          { rintros ⟨a, ha⟩ ⟨a', ha'⟩ h,
            apply heq_of_eq,
            have h' : a = a',
            { refine @congr_heq _ _ _ subtype.val subtype.val _ _ _ h,
              congr, exact H },
            dsimp, rw h',
            rw ite_eq_left_iff,
            intro h'', rw inv_eq_one_div at h'',
            rw le_antisymm ha' (le_of_not_lt h''),
            rw sub_half, simp },
          { continuity, cases x with x hx,
            apply not_lt_of_le hx,
            refine lt_of_lt_of_eq (half_lt_self zero_lt_one) _,
            rw ← sub_eq_zero, assumption } } } },
    { intros p hp, simp,
      have h1 := hp.left.left.left 0,
      have h2 : p 0 ≤ 1 := topological_simplex.coord_le_one (n + 1) 0 ⟨p, hp.left.left⟩,
      split_ifs, swap,
      { simp, rw inv_eq_one_div at h,
        replace h := le_of_not_lt h,
        exact ⟨⟨⟨hp.left.left, hp.left.right⟩, lt_of_lt_of_le (div_pos one_pos two_pos) h⟩,
               hp.left.left, h⟩ },
      { have h' : 0 ≤ 1 - (1 - p 0)⁻¹ * 2⁻¹,
        { rw [sub_nonneg, ← mul_inv],
          apply inv_le_one,
          refine le_of_eq_of_le (inv_mul_cancel_of_invertible 2).symm _,
          refine decidable.mul_le_mul_of_nonneg_right _ zero_le_two,
          rw le_sub,
          convert le_of_lt h,
          rw inv_eq_one_div, apply sub_half },
        have h'' : 0 ≤ (1 - p 0)⁻¹ * 2⁻¹,
        { rw [← mul_inv, inv_nonneg],
          refine mul_nonneg _ zero_le_two,
          rw sub_nonneg, exact h2 },
        have h''' : (1 - (1 - p 0)⁻¹ * 2⁻¹) • (vertex (n + 1) 0).val
                  + (1 - (1 - (1 - p 0)⁻¹ * 2⁻¹)) • p
                  ∈ topological_simplex_boundary (n + 1),
        { refine set.inter_subset_left _ _ 
                    (topological_simplex_boundary_minus_interior_of_bottom_face_star_convex (n + 1) 
                      hp _ _ _),
          { exact h' },
          { rw sub_sub_self, exact h'' },
          { apply add_sub_cancel'_right } },
        have h'''' : (1/2 : ℝ) ≤ (1 - (1 - p 0)⁻¹ * 2⁻¹) * (vertex (n + 1) 0).val 0
                               + (1 - (1 - (1 - p 0)⁻¹ * 2⁻¹)) * p 0,
        { rw sub_sub_self,
          apply le_of_eq,
          transitivity (1 - (1 - p 0)⁻¹ * 2⁻¹) + (1 - p 0)⁻¹ * 2⁻¹ * p 0,
          { rw inv_eq_one_div at ⊢ h, rw inv_eq_one_div, generalize hc : 1 - p 0 = c,
            rw [sub_eq_iff_eq_add, add_comm, ← sub_eq_iff_eq_add] at hc, rw ← hc at h ⊢,
            -- might be able to use a single tactic?
            rw [sub_add, ← mul_one_sub, sub_sub_self, mul_right_comm, ← inv_eq_one_div c,
                inv_mul_cancel],
            { rw one_mul, symmetry, apply sub_half },
            { intro hc', rw [hc', sub_zero] at h, exact not_lt_of_le (half_le_self zero_le_one) h } },
          { congr, convert (mul_one _).symm, exact vertex_coord_one (n + 1) 0 } }, 
        split,
        { dsimp [topological_simplex_boundary_minus_bottom_face],
          split,
          { exact h''' },
          { exact lt_of_lt_of_le (half_pos zero_lt_one) h'''' } },
        { exact ⟨h'''.left, h''''⟩ } } },
    { intros y hy u hu h,
      rw [← set.mem_compl_iff, set.compl_inter, topological_simplex_minus_bottom_half,
          set.compl_inter],
      refine set.subset_union_right _ _ (set.subset_union_right _ _ _),
      simp,
      refine @lt_of_eq_of_lt _ _ _ (u + (1 - u) * y 0) _ _ _,
      { congr, convert mul_one u, exact vertex_coord_one (n + 1) 0 },
      { dsimp at h, split_ifs at h with h',
        { have h'' := hy.left.left.left 0,
          generalize_hyp : y 0 = c at h h' h'' ⊢,
          have h''' : 0 < 1 - c,
          { rw sub_pos, refine lt_trans h' _, exact half_lt_self zero_lt_one },
          rw [one_sub_mul, add_sub_left_comm, ← mul_one_sub],
          refine lt_of_lt_of_eq (add_lt_add_left (mul_lt_mul_of_pos_right h h''') c) _,
          rw [sub_mul, one_mul, div_mul, mul_div_cancel _ (ne.symm (ne_of_lt h'''))],
          rw [add_comm, sub_right_comm, sub_add, sub_self, sub_zero], 
          rw [sub_half, inv_eq_one_div] },
        { exfalso, exact not_lt_of_le hu h } } },
    { intros y hy hy',
      simp, split_ifs,
      { apply sub_lt_self, apply mul_pos; rw inv_pos,
        { rw sub_pos, refine lt_trans h _, rw inv_eq_one_div, exact half_lt_self zero_lt_one },
        { exact zero_lt_two } },
      { exact zero_lt_one } } },
  obtain ⟨h3⟩ := coker_of_quasi_isos_between_monic_arrows_is_quasi_iso
                  ((singular_chain_complex R).map (⟨set.inclusion (set.inter_subset_left _ _),
                                                    embedding_subtype_coe.to_inducing.continuous_iff.mpr (by continuity)⟩
                                                   : Top.of s1 ⟶ Top.of (topological_simplex_boundary_minus_top_vertex (n + 1))))
                  ((singular_chain_complex R).map (⟨set.inclusion (set.inter_subset_left _ _), 
                                                    embedding_subtype_coe.to_inducing.continuous_iff.mpr (by continuity)⟩
                                                   : Top.of s2 ⟶ Top.of (topological_simplex_boundary_minus_top_vertex (n + 1))))
                  _ _ ((singular_chain_complex R).map g2) g1 h_aux2 h_aux1 _,
  swap,
  { apply_with homological_complex.mono_of_eval {instances:=ff}, 
    intro i, refine (Module.mono_iff_injective _).mpr _,
    apply singular_chain_complex_map_inj,
    apply set.inclusion_injective },
  swap,
  { apply_with homological_complex.mono_of_eval {instances:=ff}, 
    intro i, refine (Module.mono_iff_injective _).mpr _,
    apply singular_chain_complex_map_inj,
    apply set.inclusion_injective },
  swap,
  { refine eq.trans _ (category.id_comp _).symm,
    rw [← (singular_chain_complex R).map_comp],
    refl },

/-
  Hₖ(topological_simplex n, topological_simplex_boundary n)
  ⟶ Hₖ(topological_simplex_boundary_minus_top_vertex (n + 1), topological_simplex_boundary_minus_interior_of_bottom_face (n + 1) ∩ topological_simplex_boundary_minus_top_vertex (n + 1))
  ^^ conceptually iso because of deformation retraction
-/
  let g3 := include_simplex_as_bottom_face n,
  let g4 := continuous_map.comp ⟨_, continuous_inclusion (subset_of_eq (eq.trans _ s2_spec.symm))⟩
                                (include_simplex_boundary_as_bottom_face n),
  swap,
  { delta topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex
          topological_simplex_boundary_minus_interior_of_bottom_face
          topological_simplex_boundary_minus_top_vertex,
    rw [set.diff_eq, set.diff_eq, set.inter_right_comm (topological_simplex_boundary (n + 1)),
        ← set.inter_assoc, set.inter_self, set.inter_right_comm], },
  let g5 : C(s2, topological_simplex_boundary_minus_top_vertex (n + 1)) := {
    to_fun := set.inclusion (set.inter_subset_left _ _),
    continuous_to_fun := embedding_subtype_coe.to_inducing.continuous_iff.mpr (by continuity)
  },
  let g6 : @arrow.mk _ _ (Top.of (topological_simplex_boundary n)) (Top.of (topological_simplex n)) (topological_simplex_boundary_incl_topological_simplex n)
         ⟶ @arrow.mk _ _ (Top.of s2) (Top.of (topological_simplex_boundary_minus_top_vertex (n + 1))) g5 :=
      @arrow.hom_mk' _ _ (Top.of (topological_simplex_boundary n)) (Top.of (topological_simplex n))
                     _
                     (Top.of s2) (Top.of (topological_simplex_boundary_minus_top_vertex (n + 1)))
                     _ g4 g3 _,
  swap, { ext, cases x, refl },
  obtain ⟨h4⟩ := coker_of_quasi_isos_between_monic_arrows_is_quasi_iso
                  ((singular_chain_complex R).map (topological_simplex_boundary_incl_topological_simplex n))
                  (@category_theory.functor.map _ _ _ _ (singular_chain_complex R) (Top.of s2) (Top.of (topological_simplex_boundary_minus_top_vertex (n + 1))) g5)
                  (boundary_inclusion_mono_on_chains n) _
                  ((singular_chain_complex R).map g4)
                  ((singular_chain_complex R).map g3) _ _ _,
  swap,
  { apply_with homological_complex.mono_of_eval {instances:=ff}, 
    intro i, refine (Module.mono_iff_injective _).mpr _,
    apply singular_chain_complex_map_inj,
    exact set.inclusion_injective _ },
  swap,
  { apply homotopy_equiv_induces_quasi_iso,
    dsimp [g4],
    refine is_homotopy_equivalence_two_out_of_three_2 (include_simplex_boundary_as_bottom_face n)
                                                      ⟨_, continuous_inclusion _⟩ _ _,
    { refine @deformation_retraction.is_homotopy_equivalence
               (Top.of (topological_simplex_boundary n))
               (Top.of (topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex (n + 1)))
               (include_simplex_boundary_as_bottom_face n)
               (include_simplex_boundary_as_bottom_face_is_embedding n) _,
      refine deformation_retraction.transport _ _ _ _ 
              (topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex_deformation_retract_onto_bottom_face_boundary (n + 1)) _,
      simp [g4, include_simplex_boundary_as_bottom_face, include_simplex_as_bottom_face],
      apply funext, rintro ⟨p, ⟨⟨h1, _⟩, i, h2, h3⟩, _, h4⟩, dsimp at h4, ext, split, 
      { rintro ⟨_, h5⟩, dsimp at h5,
        refine ⟨⟨fin.tail p, ⟨_, _⟩, _⟩, _⟩,
        { intro x, exact h1.left _ },
        { refine eq.trans _ (eq.trans (fin.sum_univ_succ _).symm h1.right),
          rw h5, exact (zero_add _).symm },
        { refine ⟨i.pred h2, _⟩,
          dsimp [fin.tail],
          rw fin.succ_pred, exact h3 },
        { ext, cases x with x, cases x;
          simp [fin.tail, fin.cons, fin.cases, fin.induction],
          exact h5.symm } },
      { rintro ⟨⟨q, hq⟩, h⟩, 
        refine ⟨⟨⟨_, i, h2, _⟩, _, _⟩, _⟩,
        any_goals
        { rw [← h, set.coe_cod_restrict_apply, function.comp_app, function.comp_app],
          rw subtype.val_eq_coe, exact set.inter_subset_left _ _ (subtype.mem _) },
        { exact h3 },
        exact h4,
        all_goals { rw ← h, dsimp, apply fin.cons_zero } } },
    { suffices : ∀ (h : topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex (n + 1) = s2),
                 continuous_map.is_homotopy_equiv ⟨_, continuous_inclusion (subset_of_eq h)⟩,
      { exact this _ },
      intro h,
      let f : C(topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex (n + 1), s2) := ⟨_, continuous_inclusion (subset_of_eq h)⟩,
      let g : C(s2, topological_simplex_boundary_minus_interior_of_bottom_face_minus_top_vertex (n + 1)) := ⟨_, continuous_inclusion (subset_of_eq h.symm)⟩,
      change f.is_homotopy_equiv,
      refine ⟨g, ⟨continuous_map.homotopy.cast (continuous_map.homotopy.refl (continuous_map.id _))
                                              _ (refl _)⟩,
                 ⟨continuous_map.homotopy.cast (continuous_map.homotopy.refl (continuous_map.id _))
                                              _ (refl _)⟩⟩;
      { ext x, cases x, refl } } },
  swap,
  { apply homotopy_equiv_induces_quasi_iso,
    refine deformation_retraction.is_homotopy_equivalence _
             (include_simplex_as_bottom_face_is_embedding n) _,
    refine deformation_retraction.transport _ _ _ _ 
             (simplex_boundary_minus_top_vertex_deformation_retract_onto_bottom_face (n + 1)) _,
    simp [g3, include_simplex_as_bottom_face],
    apply funext, rintro ⟨p, hp⟩, ext, split,
    { rintro ⟨_, h⟩,
      refine ⟨⟨fin.tail p, _, _⟩, _⟩,
      { intro i, dsimp [fin.tail], apply hp.left.left.left },
      { refine eq.trans _ (eq.trans (fin.sum_univ_succ _).symm hp.left.left.right),
        dsimp at h, rw h, exact (zero_add _).symm },
      { apply subtype.eq, ext i, cases i with i, cases i with i;
        simp [fin.tail, fin.cons, fin.cases, fin.induction],
        exact h.symm } },
    { rintro ⟨q, hq⟩, rw ← hq,
      dsimp [topological_simplex_bottom_face],
      refine ⟨_, rfl⟩,
      have : topological_simplex_boundary_minus_top_vertex (n + 1) ⊆ topological_simplex (n + 1)
        := subset_trans (set.inter_subset_left _ _) (set.inter_subset_left _ _),
      refine this _, apply subtype.mem } },
  swap,
  { rw [← (singular_chain_complex R).map_comp, ← (singular_chain_complex R).map_comp],
    refine congr_arg _ _, 
    ext, cases a, refl },

  refine @category_theory.as_iso _ _ _ _ _ h1 ≪≫ _,
  refine i7.symm ≪≫ _,
  refine (@category_theory.as_iso _ _ _ _ _ (h2 k)).symm ≪≫ _,
  refine i6 ≪≫ _,
  refine _ ≪≫ (@category_theory.as_iso _ _ _ _ _ (h4 k)).symm,
  refine @category_theory.as_iso _ _ _ _ _ (h3 k),
end.

lemma boundary_of_zero_simplex_empty : is_empty (topological_simplex_boundary 0) :=
⟨begin
  rintro ⟨p, ⟨_, h⟩, i, h'⟩,
  have : finset.sum {(0 : fin 1)} p = 1, { refine eq.trans _ h, congr },
  rw finset.sum_singleton at this, change fin 1 at i, fin_cases i,
  exact zero_ne_one (h'.symm.trans this)
end⟩.

lemma singular_chain_complex_of_empty {R : Type*} [comm_ring R] (A : Top) (h : is_empty A) (k : ℕ)
  : limits.is_zero (((singular_chain_complex R).obj A).X k) :=
begin
  apply_with Module.is_zero_of_subsingleton {instances:=ff},
  dsimp [singular_chain_complex, free_complex_on_sset, Top.to_sSet'],
  suffices : is_empty (Top.of ↥((simplex_category.mk k).to_Top'_obj) ⟶ A),
  { obtain ⟨h⟩ := this, constructor, intros a b, ext f, exfalso, exact h f },
  constructor, rintro ⟨f, _⟩, exact is_empty.false (f (vertex k 0))
end

lemma homology_of_empty {R : Type*} [comm_ring R] (A : Top) (h : is_empty A) (k : ℕ)
  : limits.is_zero ((singular_homology R k).obj A) :=
begin
  apply_with Module.is_zero_of_subsingleton {instances:=ff},
  apply_with (@function.surjective.subsingleton _ _ Module.to_homology _ _) {instances:=ff},
  { apply_with subtype.subsingleton {instances:=ff},
    refine subsingleton_of_forall_eq 0 _,
    apply all_eq_zero_of_iso_zero,
    refine ⟨limits.is_zero.iso_zero _⟩,
    apply singular_chain_complex_of_empty, exact h },
  { intro y, obtain ⟨x, hx, H⟩ := homological_complex.exists_preim_homology_class _ y,
    exact ⟨⟨x, hx⟩, H⟩ }
end

lemma homology_of_boundary_of_zero_simplex {R : Type*} [comm_ring R] [nontrivial R] (k : ℕ)
  : limits.is_zero ((singular_homology R k).obj (Top.of (topological_simplex_boundary 0))) :=
  homology_of_empty _ boundary_of_zero_simplex_empty _

noncomputable
def equiv_fin_two_of_exactly_two_elements {α : Type*} (x0 x1 : α)
  (h1 : x0 ≠ x1) (h2 : ∀ x, x = x0 ∨ x = x1) : fin 2 ≃ α :=
  equiv.of_bijective (λ i, if i = 0 then x0 else x1)
  (begin
    refine ⟨_, _⟩,
    { intros i j, fin_cases i; fin_cases j; simp, exact h1, exact h1.symm },
    { intro x, cases h2 x with h; rw h, { exact ⟨0, rfl⟩ }, { exact ⟨1, rfl⟩ } } 
   end)

lemma vertex_mem_boundary (n : ℕ) (hn : 0 < n) (i : fin (n + 1))
  : (vertex n i).val ∈ topological_simplex_boundary n :=
begin
  rw subtype.val_eq_coe, refine ⟨subtype.mem _, _⟩,
  let j : fin (n + 1) := if i = 0 then 1 else 0,
  existsi j,
  refine vertex_coord_zero n i j _,
  dsimp [j], split_ifs,
  { rw h, cases n, cases hn, exact fin.zero_ne_one },
  { exact h }
end

lemma boundary_of_one_simplex_desc (x : topological_simplex_boundary 1)
  : x = ⟨(vertex 1 0).val, vertex_mem_boundary 1 zero_lt_one 0⟩
  ∨ x = ⟨(vertex 1 (1 : fin 2)).val, vertex_mem_boundary 1 zero_lt_one 1⟩ :=
begin
  rcases x with ⟨p, hp, i, hi⟩,
  let j : fin 2 := if i = 0 then 1 else 0,
  suffices : (⟨p, hp⟩ : topological_simplex 1) = vertex 1 j,
  { replace this := congr_arg subtype.val this, fin_cases j; rw this_1 at this,
    { left, apply subtype.eq, exact this },
    { right, apply subtype.eq, exact this } },
  apply eq_vertex,
  refine eq.trans _ hp.right,
  refine eq.trans _ (@finset.sum_filter_of_ne _ _ _ _ _ (λ k, j = k) _ _),
  { rw finset.filter_eq, simp },
  { intros k _ hk,
    have hk' : k ≠ i, { intro h', rw h' at hk, exact hk hi },
    dsimp [j], change fin 2 at i, fin_cases i; fin_cases k; try { contradiction }; simp }
end

noncomputable
def zeroth_homology_of_boundary_of_one_simplex {R : Type*} [comm_ring R] [nontrivial R]
  : (singular_homology R 0).obj (Top.of (topological_simplex_boundary 1))
  ≅ (Module.free R).obj (fin 2) :=
begin
  refine linear_equiv.to_Module_iso'_left _,
  apply_with (linear_equiv.trans (singular_homology0_basis R _).repr
                                 (finsupp.dom_lcongr _)) {instances:=ff},
  symmetry,
  let x0 : topological_simplex_boundary 1 := ⟨(vertex 1 0).val, vertex_mem_boundary 1 zero_lt_one 0⟩,
  let x1 : topological_simplex_boundary 1 := ⟨(vertex 1 (1 : fin 2)).val, vertex_mem_boundary 1 zero_lt_one 1⟩,
  refine equiv_fin_two_of_exactly_two_elements
           (quot.mk (path_setoid (topological_simplex_boundary 1)).r x0)
           (quot.mk (path_setoid (topological_simplex_boundary 1)).r x1) _ _; dsimp [x0, x1],
  { intro h,
    obtain ⟨⟨p, h1, h2⟩⟩ := @quotient.exact _ (path_setoid (topological_simplex_boundary 1)) _ _ h,
    let f := continuous_map.comp ⟨_, continuous_apply (1 : fin 2)⟩
              (continuous_map.comp ⟨_, continuous_subtype_val⟩ 
              (continuous_map.comp ⟨_, continuous_inclusion (set.inter_subset_left _ _)⟩ p)),
    let g : ℝ → ℝ := λ t, f.to_fun ⟨min (max 0 t) 1, le_min (le_max_left _ _) zero_le_one, min_le_right _ _⟩,
    have Hg : continuous g,
    { refine continuous.comp f.continuous_to_fun (continuous_subtype_mk _ _), continuity },
    have := @intermediate_value_Icc _ _ _ _ _ _ _ _ _ 0 1 zero_le_one g Hg.continuous_on,
    have h1 : g 0 = 0,
    { simp [g, f],
      transitivity (p (0 : I)).val (1 : fin 2), { congr, simp },
      { change (p.to_fun 0).val (1 : fin 2) = 0, rw h1, exact vertex_coord_zero 1 _ _ fin.zero_ne_one } },
    have h2 : g 1 = 1,
    { simp [g, f],
      transitivity (p (1 : I)).val (1 : fin 2), { congr, simp },
      { change (p.to_fun 1).val (1 : fin 2) = 1, rw h2, exact vertex_coord_one 1 _ } },
    rw [h1, h2] at this,
    obtain ⟨t, ht1, ht2⟩ := this half_mem_unit_interval,
    simp [g, f] at ht2,
    have ht3 : (p.to_fun ⟨t, ht1⟩).val (1 : fin 2) = 2⁻¹,
    { refine eq.trans _ ht2, congr, rw [max_eq_right ht1.left, min_eq_left ht1.right] },
    cases boundary_of_one_simplex_desc (p.to_fun ⟨t, ht1⟩) with H H;
    rw H at ht3; dsimp [x0, x1] at ht3,
    { have := eq.trans (vertex_coord_zero 1 0 (1 : fin 2) fin.zero_ne_one).symm ht3, simp at this, exact this },
    { have := eq.trans (vertex_coord_one 1 (1 : fin 2)).symm ht3, simp at this, 
      norm_cast at this, simp at this, exact this } },
  { intro q, induction q, cases boundary_of_one_simplex_desc q with H H; rw H,
    left, refl, right, refl, refl }
end.

lemma zeroth_homology_of_boundary_of_one_simplex_spec {R : Type*} [comm_ring R] [nontrivial R]
  : ∀ i,
   (@zeroth_homology_of_boundary_of_one_simplex R _ _).inv (finsupp.single i 1)
  = (singular_homology0_basis R (Top.of (topological_simplex_boundary 1)))
    (quot.mk (path_setoid (topological_simplex_boundary 1)).r
      ⟨(vertex 1 i).val, vertex_mem_boundary 1 zero_lt_one i⟩) :=
begin
  intro i, fin_cases i;
  dsimp [zeroth_homology_of_boundary_of_one_simplex];
  refine congr_arg _ _;
  simp [equiv_fin_two_of_exactly_two_elements, finsupp.dom_lcongr]
end

-- Move this
def Top.coprod_binary_cofan (X Y : Top.{u}) : limits.binary_cofan X Y :=
  @limits.binary_cofan.mk Top _ X Y (Top.of (X ⊕ Y)) ⟨sum.inl⟩ ⟨sum.inr⟩

def Top.coprod_binary_cofan_is_colimit (X Y : Top.{u})
  : limits.is_colimit (Top.coprod_binary_cofan X Y) := {
  desc := λ (s : limits.binary_cofan X Y), ⟨sum.elim s.inl s.inr⟩,
  fac' := begin
    rintros S (_|_),
    tidy
  end,
  uniq' := begin
    intros S m h,
    ext x, cases x,
    { specialize h ⟨limits.walking_pair.left⟩,
      apply_fun (λ e, (e x)) at h,
      exact h },
    { specialize h ⟨limits.walking_pair.right⟩,
      apply_fun (λ e, (e x)) at h,
      exact h },
  end
}.

noncomputable
def Top.coprod_iso_coprod (X Y : Top.{u}) : X ⨿ Y ≅ Top.of (X ⊕ Y) :=
(limits.colimit.is_colimit _).cocone_point_unique_up_to_iso (Top.coprod_binary_cofan_is_colimit X Y).

local attribute [instance] classical.prop_decidable
noncomputable
def two_point_t2_space_homeo_coprod_two_points {α : Type*} [topological_space α] [t1_space α]
  (x0 x1 : α) (h1 : x0 ≠ x1) (h2 : ∀ x, x = x0 ∨ x = x1)
  : punit ⊕ punit ≃ₜ α := {
    to_fun := sum.elim (λ _, x0) (λ _, x1),
    inv_fun := λ x, if x = x0 then sum.inl () else sum.inr (),
    left_inv := by { rintro (_|_), tidy },
    right_inv := by { intro x, cases h2 x with H H; subst H; simp; split_ifs; simp, exact h.symm },
    continuous_inv_fun := by { letI : fintype α := ⟨{x0, x1}, by { simp, exact h2 }⟩,
                               letI := @discrete_of_t1_of_finite α _ _ _,
                               exact continuous_of_discrete_topology }
  }.

instance preserves_colimits_of_discrete_shape_of_preserves_colimit_of_discrete_functor
  {C : Type*} [category C] {D : Type*} [category D] (F : C ⥤ D)
  (J : Type*) (H : ∀ f : J → C, limits.preserves_colimit (discrete.functor f) F)
  : limits.preserves_colimits_of_shape (discrete J) F := 
  ⟨λ K, limits.preserves_colimit_of_iso_diagram _ discrete.nat_iso_functor.symm⟩

instance preserves_binary_coproducts_of_preserves_finite_coproducts 
  {C : Type*} [category C] {D : Type*} [category D] (F : C ⥤ D)
  (H : ∀ {J : Type} [fintype J], limits.preserves_colimits_of_shape (discrete J) F)
  : ∀ {X Y : C}, limits.preserves_colimit (limits.pair X Y) F :=
  by { intros, specialize @H limits.walking_pair _, cases H, exact @H _ }

lemma homology_rel_empty_iso_homology {R : Type*} [comm_ring R] {A X : Top} (i : A ⟶ X)
  (h : is_empty A) (k : ℕ)
  : is_iso ((singular_homology_of_base_to_of_pair R k).app (arrow.mk i)) :=
begin
  delta singular_homology_of_base_to_of_pair,
  rw nat_trans.comp_app,
  delta functor.associator,
  unfold_projs,
  dsimp, rw linear_map.comp_id,
  apply_with quasi_iso.is_iso {instances:=ff},
  apply_with quasi_iso_of_iso {instances:=ff},
  dsimp [coker_functor_proj],
  apply_with balanced.is_iso_of_mono_of_epi {instances:=ff},
  { apply_instance },
  { rw homological_complex.mono_iff_eval, intro n,
    let H1 := coker_of_chain_map_at_is_colimit ((singular_chain_complex R).map i) n,
    let F1 : limits.cokernel (((singular_chain_complex R).map i).f n)
         ≅ (coker_of_chain_map_at ((singular_chain_complex R).map i) n).X :=
      (limits.colimit.is_colimit _).cocone_point_unique_up_to_iso H1,
    apply_with (mono_of_mono _ F1.inv) {instances:=ff},
    simp [F1, limits.is_colimit.cocone_point_unique_up_to_iso],
    convert @is_iso.mono_of_iso _ _ _ _ _ (limits.coequalizer.π_of_eq _),
    { refine (iso.comp_inv_eq F1).mpr _,
      simp [F1],
      delta limits.cokernel.π limits.cofork.π limits.coequalizer.π,
      dsimp [coker_of_chain_map_at, parallel_pair_comp.cocone_comp_to_cocone_pair], 
      simp,
      symmetry, exact category.id_comp _ },
    { apply limits.is_zero.eq_of_src,
      apply singular_chain_complex_of_empty,
      exact h } },
  { apply_instance }
end

lemma higher_homology_of_zero_simplex {R : Type*} [comm_ring R] (k : ℕ) (hk : 0 < k)
  : limits.is_zero ((singular_homology R k).obj (Top.of (topological_simplex 0))) :=
begin
  refine limits.is_zero_of_iso_of_zero (limits.is_zero_zero _) _,
  symmetry, refine nonempty.some _,
  apply homology_of_contractible_space R _ _ k hk,
  refine ⟨⟨homeomorph.to_homotopy_equiv ⟨_, _, _⟩⟩⟩,
  { dsimp, exact equiv.equiv_punit (topological_simplex 0)},
  { dsimp [equiv.equiv_punit, equiv.equiv_of_unique], continuity },
  { dsimp [equiv.equiv_punit, equiv.equiv_of_unique], continuity }
end

lemma higher_homology_of_boundary_of_one_simplex {R : Type*} [comm_ring R] [nontrivial R]
  (k : ℕ) (hk : 0 < k)
  : limits.is_zero ((singular_homology R k).obj (Top.of (topological_simplex_boundary 1))) :=
begin
  refine limits.is_zero_of_iso_of_zero _ (iso.symm (homology_rel_boundary_iso_homology_of_boundary 0 k hk)),
  refine limits.is_zero_of_iso_of_zero _ 
          (@as_iso _ _ _ _ _ (homology_rel_empty_iso_homology _ _ _)),
  { apply higher_homology_of_zero_simplex, exact hk },
  { exact boundary_of_zero_simplex_empty }
end.

lemma boundary_of_simplex_path_connected (n : ℕ) (hn : n > 1)
  : path_connected_space (topological_simplex_boundary n) :=
begin
  rw path_connected_space_iff_eq,
  let v : fin (n + 1) → topological_simplex_boundary n
      := λ i, ⟨vertex n i, vertex_mem_boundary n (zero_lt_one.trans hn) i⟩,
  refine ⟨v 0, _⟩,
  suffices : (∀ x, ∃ i, joined x (v i)) ∧ (∀ i, joined (v 0) (v i)),
  { cases this with h1 h2, ext x, simp,
    obtain ⟨i, hi⟩ := h1 x, specialize h2 i, exact h2.trans hi.symm },
  split,
  { rintro ⟨x, hx⟩, have H := (@zero_ne_one ℝ _ _).symm, rw ← hx.left.right at H,
    obtain ⟨i, _, hi⟩ := finset.exists_ne_zero_of_sum_ne_zero H, dsimp at hi,
    existsi i,
    obtain ⟨j, hj⟩ := hx.right,
    refine joined_in.joined_subtype _,
    let γ : C(unit_interval, fin (n + 1) → ℝ) := ⟨λ t k, if k = i then (1 - x i) * t + x i else (1 - t) * x k, _⟩,
    swap, { continuity, apply continuous_if_const; intro; continuity },
    refine ⟨⟨γ, _, _⟩, (λ t, ⟨⟨_, _⟩, j, _⟩)⟩,
    { ext k, simp [γ], intro h, subst h },
    { ext k, simp [γ], split_ifs,
      { subst h, exact (vertex_coord_one n k).symm }, 
      { exact (vertex_coord_zero n i k (ne.symm h)).symm } },
    { intro k, simp [γ], split_ifs,
      { subst h, refine add_nonneg (mul_nonneg _ (unit_interval.nonneg t)) (hx.left.left k),
        rw sub_nonneg, exact topological_simplex.coord_le_one n k ⟨x, hx.left⟩ },
      { exact mul_nonneg (unit_interval.one_minus_nonneg t) (hx.left.left k) } },
    { simp [γ], refine eq.trans (finset.sum_ite _ _) _,
      rw [finset.filter_eq', finset.filter_ne'], simp,
      rw [← finset.mul_sum, hx.left.right],
      ring },
    { simp [γ], split_ifs, { exfalso, rw h at hj, exact hi hj }, { rw hj, exact mul_zero _ } } },
  { intro i, refine joined_in.joined_subtype _,
    refine @joined_in.mono _ _ _ _ (topological_simplex_boundary_minus_interior_of_bottom_face n) _ _ (set.inter_subset_left _ _),
    { have : ∀ j, (v j).val ∈ topological_simplex_boundary_minus_interior_of_bottom_face n,
      { intro j, rw subtype.val_eq_coe, refine ⟨subtype.mem _, _⟩, 
        let k := if j = fin.last n then 1 else j + 1,
        cases n, { exfalso, exact lt_asymm zero_lt_one hn },
        cases n, { exfalso, exact lt_irrefl _ hn },
        refine ⟨k, _, vertex_coord_zero (n+2) j k _⟩;
        dsimp [k]; split_ifs; try { exact fin.zero_ne_one.symm };
        try { rw h, refine ne.symm (@ne_of_lt (fin (n + 3)) _ _ _ (fin.cast_succ_lt_last (1 : fin (n + 2)))) };
        rw [subtype.ext_iff, fin.coe_add_one];
        simp_rw [eq_false_intro h]; simp },
      rw joined_in_iff_joined (this 0) (this i),
      haveI := star_convex.contractible_space (topological_simplex_boundary_minus_interior_of_bottom_face_star_convex n)
                                              ⟨(v 0).val, this 0⟩,
      apply path_connected_space.joined } }
end.

-- should extract proof that ∂Δ^n is path connected for n > 1
noncomputable
def zeroth_homology_of_boundary_of_n_simplex {R : Type*} [comm_ring R] [nontrivial R] (n : ℕ)
  (hn : n > 1) : (singular_homology R 0).obj (Top.of (topological_simplex_boundary n))
  ≅ Module.of R R :=
begin
  transitivity (Module.free R).obj (fin 1),
  { refine linear_equiv.to_Module_iso'_left _,
    apply_with (linear_equiv.trans (singular_homology0_basis R _).repr
                                  (finsupp.dom_lcongr _)) {instances:=ff},
    symmetry,
    refine fin_one_equiv.trans (equiv.symm _),
    apply_with equiv.equiv_punit {instances:=ff},
    refine nonempty.some _,
    rw [unique_iff_subsingleton_and_nonempty, and.comm, ← path_connected_space_iff_zeroth_homotopy],
    exact boundary_of_simplex_path_connected n hn },
  { refine linear_equiv.to_Module_iso _,
    -- extract this
    refine ⟨(λ f, f 0), _, _, (λ r, finsupp.single 0 r), _, _⟩,
    { intros, refl },
    { intros, refl },
    { intro, ext, simp },
    { intro, simp } }
end.

noncomputable
def first_homology_of_boundary_of_two_simplex {R : Type*} [comm_ring R] [nontrivial R]
  : (singular_homology R 1).obj (Top.of (topological_simplex_boundary 2))
  ≅ Module.of R R :=
begin
  refine iso.trans (homology_rel_boundary_iso_homology_of_boundary 1 1 zero_lt_one) _,
  let i := (singular_chain_complex R).map (topological_simplex_boundary_incl_topological_simplex 1),
  -- this comes up a lot, should probably be a lemma
  haveI : mono i := boundary_inclusion_mono_on_chains 1,
  let δ := homological_complex.δ i ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                                   (coker_functor_degreewise_SES i) 1 0 rfl,
  have LES : exact_seq (Module R) [arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) 1).map ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))),
                                   arrow.mk δ, 
                                   arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) 0).map i)] :=
              (homological_complex.six_term_exact_seq i
                 ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                 (coker_functor_degreewise_SES i) 1 0 rfl).extract 1 3,
  have hw := ((exact_iff_exact_seq _ _).mpr (LES.extract 1 2)).w,
  letI := exact.mono_of_eq_zero ((exact_iff_exact_seq _ _).mpr (LES.extract 0 2)) _,
  swap,
  { apply limits.is_zero.eq_of_src, 
    refine limits.is_zero_of_iso_of_zero (limits.is_zero_zero _) _,
    symmetry, refine nonempty.some _,
    apply homology_of_contractible_space R _ _ 1 zero_lt_one,
    exact (convex_std_simplex ℝ (fin 2)).contractible_space ⟨(vertex 1 0).val, (vertex 1 0).property⟩ },
  letI := (exact_iff_image_to_kernel'_is_iso _ _ hw).mp
            ((exact_iff_exact_seq _ _).mpr (LES.extract 1 2)),
  
  refine (limits.image_mono_iso_source δ).symm
         ≪≫ as_iso ((image_to_kernel' δ ((homology_functor (Module R) (complex_shape.down ℕ) 0).map i) hw))
         ≪≫ Module.kernel_iso_ker _
         ≪≫ linear_equiv.to_Module_iso'_right _,
  symmetry,
  let b := @zeroth_homology_of_boundary_of_one_simplex R _ _,
  let v1 := b.inv (finsupp.single 0 1),
  let v2 := b.inv (finsupp.single 1 1),
  let x0 : topological_simplex_boundary 1 :=
        ⟨(vertex 1 0).val, vertex_mem_boundary 1 zero_lt_one 0⟩,
  let x1 : topological_simplex_boundary 1 :=
      ⟨(vertex 1 (1 : fin 2)).val, vertex_mem_boundary 1 zero_lt_one (1 : fin 2)⟩,
  have : v1 - v2 ∈ linear_map.ker ((homology_functor (Module R) (complex_shape.down ℕ) 0).map i),
  { dsimp [v1, v2, b],
    rw [zeroth_homology_of_boundary_of_one_simplex_spec, zeroth_homology_of_boundary_of_one_simplex_spec],
    rw [linear_map.mem_ker, map_sub],
    rw sub_eq_zero,
    change (singular_homology R 0).map (topological_simplex_boundary_incl_topological_simplex 1)
             (singular_homology0_basis R (Top.of (topological_simplex_boundary 1))
               (quot.mk (path_setoid (topological_simplex_boundary 1)).r x0))
           = (singular_homology R 0).map (topological_simplex_boundary_incl_topological_simplex 1)
               (singular_homology0_basis R (Top.of (topological_simplex_boundary 1))
                 (quot.mk (path_setoid (topological_simplex_boundary 1)).r x1)),
    rw [singular_homology0_map_matrix, singular_homology0_map_matrix],
    refine congr_arg _ _,
    apply quot.sound,
    apply_with path_connected_space.joined {instances:=ff},
    apply_with contractible_space.path_connected_space {instances:=ff},
    exact (convex_std_simplex ℝ (fin 2)).contractible_space ⟨(vertex 1 0).val, (vertex 1 0).property⟩ },
  refine linear_equiv.of_bijective ⟨λ r, r • ⟨v1 - v2, this⟩, _, _⟩ _ _,
  { intros, apply subtype.eq, apply add_smul, },
  { intros, apply subtype.eq, simp, apply mul_smul },
  { rw [← linear_map.ker_eq_bot, linear_map.ker_eq_bot'],
    intros r hr, simp at hr,
    have hr' : r • (v1 - v2) = 0 := congr_arg subtype.val hr,
    rw smul_sub at hr',
    dsimp [v1, v2] at hr',
    rw [← map_smul, ← map_smul, ← map_sub] at hr',
    replace hr' := congr_arg b.hom hr',
    rw [← comp_apply, b.inv_hom_id, map_zero] at hr',
    simp only [mul_one, finsupp.smul_single', Module.id_apply] at hr',
    rw [sub_eq_zero, finsupp.single_eq_single_iff] at hr',
    simp at hr',
    exact hr' },
  { rintro ⟨y, hy⟩,
    dsimp,
    suffices : ∃ a : R, a • (v1 - v2) = y, { cases this with a ha, exact ⟨a, subtype.eq ha⟩ },
    have : ∃ r s : R, b.hom y = r • finsupp.single 0 1 + s • finsupp.single 1 1,
    { refine ⟨(b.hom y).to_fun 0, (b.hom y).to_fun 1, _⟩, ext i, fin_cases i; simp; refl },
    obtain ⟨r, s, h⟩ := this, replace h := congr_arg b.inv h,
    rw [← comp_apply, b.hom_inv_id, Module.id_apply, map_add, map_smul, map_smul] at h,
    rw h at hy,
    dsimp [b] at hy,
    rw [zeroth_homology_of_boundary_of_one_simplex_spec, zeroth_homology_of_boundary_of_one_simplex_spec] at hy,
    rw [linear_map.mem_ker, map_add, map_smul, map_smul] at hy,
    have H : r • (singular_homology R 0).map (topological_simplex_boundary_incl_topological_simplex 1)
                 (singular_homology0_basis R (Top.of (topological_simplex_boundary 1))
                   (quot.mk (path_setoid (topological_simplex_boundary 1)).r x0))
           + s • (singular_homology R 0).map (topological_simplex_boundary_incl_topological_simplex 1)
                   (singular_homology0_basis R (Top.of (topological_simplex_boundary 1))
                     (quot.mk (path_setoid (topological_simplex_boundary 1)).r x1)) 
           = 0,
    { refine eq.mp _ hy, congr },
    have H' := H,
    rw [singular_homology0_map_matrix, singular_homology0_map_matrix] at H',
    have H'' : quot.mk (path_setoid (topological_simplex 1)).r
                 (topological_simplex_boundary_incl_topological_simplex 1 x0)
             = quot.mk (path_setoid (topological_simplex 1)).r
                 (topological_simplex_boundary_incl_topological_simplex 1 x1),
    { apply quot.sound,
      apply_with path_connected_space.joined {instances:=ff},
      apply_with contractible_space.path_connected_space {instances:=ff},
      exact (convex_std_simplex ℝ (fin 2)).contractible_space ⟨(vertex 1 0).val, (vertex 1 0).property⟩ },
    rw [H'', ← add_smul, ← basis.repr_symm_single] at H',
    rw [linear_equiv.symm_apply_eq, map_zero] at H',
    rw [finsupp.single_eq_zero, ← eq_neg_iff_add_eq_zero] at H',
    existsi r,
    rw [h, H'],
    dsimp [v1, v2], rw [neg_smul, neg_smul, smul_sub, neg_sub, sub_eq_neg_add] }
end.

lemma simplex_rel_boundary_connecting_homomorphism_is_iso (R : Type*) [comm_ring R]
  (n k : ℕ) (hk : k > 0)
  : is_iso (singular_homology_connecting_homomorphism R k (topological_simplex_boundary_incl_topological_simplex n) (set.inclusion_injective _)) :=
begin
  let i := (singular_chain_complex R).map (topological_simplex_boundary_incl_topological_simplex n),
  -- this comes up a lot, should probably be a lemma
  haveI : mono i := boundary_inclusion_mono_on_chains n,
  let δ := homological_complex.δ i ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                                   (coker_functor_degreewise_SES i) (k+1) k rfl,
  have LES : exact_seq (Module R) [arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) (k+1)).map ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))),
                                   arrow.mk δ, 
                                   arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) k).map i)] :=
              (homological_complex.six_term_exact_seq i
                 ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                 (coker_functor_degreewise_SES i) (k+1) k rfl).extract 1 3,
  
  refine is_iso_of_exact_of_is_zero_of_is_zero _ _ _ _ _ LES;
  refine limits.is_zero_of_iso_of_zero (limits.is_zero_zero _) _;
  symmetry;
  refine nonempty.some _,
  { apply homology_of_contractible_space R _ _ (k+1) (nat.zero_lt_succ k),
    exact (convex_std_simplex ℝ (fin (n+1))).contractible_space ⟨(vertex n 0).val, (vertex n 0).property⟩ },
  { apply homology_of_contractible_space R _ _ k hk,
    exact (convex_std_simplex ℝ (fin (n+1))).contractible_space ⟨(vertex n 0).val, (vertex n 0).property⟩ }
end

lemma homology_of_boundary_iso_drop_degree (R : Type*) [comm_ring R] [nontrivial R]
  (n k : ℕ) (hk : k > 0)
  : is_iso ((homology_rel_boundary_iso_homology_of_boundary n (k+1) (nat.zero_lt_succ k)).hom
           ≫ singular_homology_connecting_homomorphism R k (topological_simplex_boundary_incl_topological_simplex n)
                                                           (set.inclusion_injective _)) :=
begin
  apply_with is_iso.comp_is_iso {instances:=ff},
  { apply_instance },
  { apply simplex_rel_boundary_connecting_homomorphism_is_iso, assumption }
end

lemma dom_is_zero_of_exact_of_is_zero_of_mono {V : Type*} [category V] [abelian V]
  {A B C D : V} {f : A ⟶ B} {g : B ⟶ C} {h : C ⟶ D}
  (e : exact_seq V [f, g, h]) (h1 : limits.is_zero A) (h2 : mono h)
  : limits.is_zero B :=
begin
  haveI : mono g := exact.mono_of_eq_zero ((exact_iff_exact_seq _ _).mpr (e.extract 0 2))
                                          (limits.is_zero.eq_zero_of_src h1 _),
  rw [limits.is_zero_iff_id_eq_zero, ← cancel_mono g, category.id_comp, limits.zero_comp],
  exact exact.eq_zero_of_mono ((exact_iff_exact_seq _ _).mpr (e.extract 1 2)) h2
end

lemma homology_of_boundary_is_zero (R : Type*) [comm_ring R] [nontrivial R]
  (n k : ℕ) (hk1 : k > 0) (hk2 : k + 1 ≠ n)
  : limits.is_zero ((singular_homology R k).obj (Top.of (topological_simplex_boundary n))) :=
begin
  cases n with n, { apply homology_of_boundary_of_zero_simplex },
  revert k hk1 hk2, induction n with n ih; intros,
  { apply higher_homology_of_boundary_of_one_simplex, exact hk1 },
  { cases k, { exfalso, exact lt_irrefl _ hk1 },
    rw nat.add_one at hk2, simp at hk2,
    refine limits.is_zero_of_iso_of_zero _ (homology_rel_boundary_iso_homology_of_boundary n.succ k.succ hk1).symm,
    
    let i := (singular_chain_complex R).map (topological_simplex_boundary_incl_topological_simplex n.succ),
    -- this comes up a lot, should probably be a lemma
    haveI : mono i := boundary_inclusion_mono_on_chains n.succ,
    let δ := homological_complex.δ i ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                                    (coker_functor_degreewise_SES i) k.succ k rfl,
    have LES : exact_seq (Module R) [arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) k.succ).map ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))),
                                    arrow.mk δ, 
                                    arrow.mk ((homology_functor (Module R) (complex_shape.down ℕ) k).map i)] :=
                (homological_complex.six_term_exact_seq i
                  ((coker_functor_proj (chain_complex (Module R) ℕ)).app (arrow.mk i))
                  (coker_functor_degreewise_SES i) k.succ k rfl).extract 1 3,
    have H : k > 0 ∨ (k = 0 ∧ n > 0),
    { rw or_iff_not_imp_left,
      intro h,
      have h' : k = 0,
      { cases k with j, { refl }, { exfalso, exact h (nat.zero_lt_succ j) } },
      refine ⟨h', _⟩,
      rw h' at hk2, destruct n,
      { intro h', exfalso, exact hk2 h'.symm },
      { intros j h', rw h', exact nat.zero_lt_succ j } },
    cases H,
    { apply dom_is_zero_of_exact_of_is_zero_of_mono LES,
      { refine limits.is_zero_of_iso_of_zero (limits.is_zero_zero _) _,
        symmetry, refine nonempty.some _,
        apply homology_of_contractible_space R _ _ k.succ (nat.zero_lt_succ k),
        exact (convex_std_simplex ℝ (fin (n+2))).contractible_space ⟨(vertex (n+1) 0).val, (vertex (n+1) 0).property⟩ },
      { apply limits.is_initial.mono_from, apply limits.is_zero.is_initial,
        exact ih k H (nat.succ_ne_succ.mpr hk2) } },
    { cases H with H' H, subst H',
      apply dom_is_zero_of_exact_of_is_zero_of_mono LES,
      { refine limits.is_zero_of_iso_of_zero (limits.is_zero_zero _) _,
        symmetry, refine nonempty.some _,
        apply homology_of_contractible_space R _ _ 1 nat.zero_lt_one,
        exact (convex_std_simplex ℝ (fin (n+2))).contractible_space ⟨(vertex (n+1) 0).val, (vertex (n+1) 0).property⟩ },
      { rw [Module.mono_iff_ker_eq_bot, linear_map.ker_eq_bot'],
        intros m hm,
        let b := singular_homology0_basis R (Top.of (topological_simplex_boundary n.succ)),
        let x0 : topological_simplex_boundary (n+1) := ⟨(vertex (n+1) 0).val, vertex_mem_boundary (n+1) (nat.zero_lt_succ n) 0⟩,
        let b0 := b (quot.mk (path_setoid (topological_simplex_boundary (n+1))).r x0),
        let r := @basis.coord (zeroth_homotopy (topological_simplex_boundary (n+1))) R
                              ((singular_homology R 0).obj (Top.of (topological_simplex_boundary n.succ)))
                              _ _ _ b
                              (quot.mk (path_setoid (topological_simplex_boundary (n+1))).r x0) m, 
        have : m = r • b0,
        { apply @basis.ext_elem (zeroth_homotopy (topological_simplex_boundary (n+1))) R
                                ((singular_homology R 0).obj (Top.of (topological_simplex_boundary n.succ)))
                                _ _ _ b,
          intro i,
          have : i = (quot.mk (path_setoid (topological_simplex_boundary (n+1))).r x0),
          { induction i,
            { apply quot.sound,
              apply_with path_connected_space.joined {instances:=ff},
              apply boundary_of_simplex_path_connected,
              simp only [lt_add_iff_pos_left, gt_iff_lt],
              exact H },
            { refl } },
          rw this, simp [r, b0] },
        rw this at hm ⊢,
        rw map_smul at hm, 
        suffices : r = 0, { rw this, exact zero_smul _ _ },
        have H' : r • (singular_homology R 0).map (topological_simplex_boundary_incl_topological_simplex n.succ)
                        (singular_homology0_basis R (Top.of (topological_simplex_boundary n.succ))
                          (quot.mk (path_setoid (topological_simplex_boundary n.succ)).r x0))
                = 0,
        { refine eq.mp _ hm, congr },
        rw [singular_homology0_map_matrix, ← basis.repr_symm_single,
            linear_equiv.symm_apply_eq, map_zero, finsupp.single_eq_zero] at H',
        exact H' } } }
end.

noncomputable
def nth_homology_of_boundary_of_n_plus_one_simplex {R : Type*} [comm_ring R] [nontrivial R]
  (n : ℕ) (hn : n > 0)
  : (singular_homology R n).obj (Top.of (topological_simplex_boundary (n + 1)))
  ≅ Module.of R R :=
begin
  cases n, { exfalso, exact lt_irrefl 0 hn }, clear hn,
  induction n with n ih,
  { exact first_homology_of_boundary_of_two_simplex },
  { exact @as_iso _ _ _ _ _ (homology_of_boundary_iso_drop_degree R (n+2) (n+1) (nat.zero_lt_succ n))
          ≪≫ ih }
end.

def take_linear_combination (R : Type*) {E : Type*} [semiring R]
  [add_comm_monoid E] [module R E] {ι : Type*} [fintype ι] (v : ι → E) : (ι → R) → E :=
  finset.univ.sum (λ (x : ι), (@linear_map.proj R ι _ (λ _, R) _ _ x).smul_right (v x))

lemma take_linear_combination_cont {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {ι : Type*} [fintype ι] (v : ι → E) : continuous (take_linear_combination ℝ v) :=
begin
  dsimp [take_linear_combination],
  convert continuous_finset_sum (finset.univ : finset ι)
                                (_ : ∀ i : ι, i ∈ finset.univ → continuous (λ (c : ι → ℝ), c i • v i)),
  { ext, rw fintype.sum_apply },
  { intros, continuity }
end

lemma take_linear_combination_image_of_std_simplex (R : Type*) {E : Type*} [linear_ordered_field R]
  [add_comm_group E] [module R E] {ι : Type*} [fintype ι] (v : ι → E)
  : take_linear_combination R v '' (std_simplex R ι) = convex_hull R (set.range v) :=
begin
  rw set.finite.convex_hull_eq_image (set.finite_range v),
  let F : (ι → R) → (set.range v → R) := λ f c, (finset.filter (λ (a : ι), v a = c.val) finset.univ).sum (λ (a : ι), f a),
  suffices : F '' std_simplex R ι = std_simplex R (set.range v),
  { convert eq.trans _ (congr_arg _ this),
    rw ← set.image_comp, congr,
    ext, simp [take_linear_combination, F],
    transitivity finset.univ.sum (λ (c : set.range v), (finset.filter (λ (a : ι), v a = (c : E)) finset.univ).sum (λ a, x a • (c : E))),
    { symmetry, convert (finset.sum_fiberwise finset.univ (λ a, (⟨v a, set.mem_range_self a⟩ : set.range v)) (λ a, x a • v a)),
      ext c, apply finset.sum_congr,
      { congr, ext, rw subtype.ext_iff, refl },
      { intros a ha, simp at ha, rw ← ha, refl } },
    { congr, ext, rw finset.sum_smul } },
  { apply subset_antisymm,
    { rw set.image_subset_iff,
      rintros x hx,
      refine ⟨_, _⟩,
      { intros, refine finset.sum_nonneg _, intros, apply hx.left },
      { convert eq.trans (finset.sum_fiberwise finset.univ (λ a, (⟨v a, set.mem_range_self a⟩ : set.range v)) x) hx.right,
        dsimp [F], ext, congr, ext, rw subtype.ext_iff, refl } },
    { intros x hx,
      by_cases nonempty ι,
      { haveI := h,
        let g := function.inv_fun v,
        refine ⟨(λ a, if a = g (v a) then x ⟨v a, set.mem_range_self a⟩ else 0), ⟨_, _⟩, _⟩,
        { intros, simp, split_ifs, apply hx.left, refl },
        { refine eq.trans (finset.sum_filter _ _).symm (eq.trans _ hx.right),
          refine finset.sum_bij' (λ a _, (⟨v a, set.mem_range_self a⟩ : set.range v)) _ _ (λ c _, g c.val) _ _ _,
          { intros, exact finset.mem_univ _ },
          { intros, simp },
          { rintros ⟨c, hc⟩ _, simp, exact congr_arg g (eq.symm (function.inv_fun_eq hc)) },
          { intros a ha, simp at ha ⊢, exact ha.symm },
          { rintros ⟨c, hc⟩ _, exact subtype.eq (function.inv_fun_eq hc) } },
        { ext c, cases c with c hc, simp [F], refine eq.trans (finset.sum_filter _ _).symm _,
          rw finset.filter_filter,
          transitivity (finset.filter (λ (a : ι), a = g c) finset.univ).sum (λ (a : ι), x ⟨v a, set.mem_range_self a⟩),
          { congr, ext a, split; intro h, { rw [h.right, h.left], refl },
            { subst h, simp, refine ⟨function.inv_fun_eq hc, congr_arg _ (eq.symm (function.inv_fun_eq hc))⟩ } },
          { rw finset.filter_eq' finset.univ (g c), simp, congr, exact function.inv_fun_eq hc } } },
      { exfalso, 
        obtain ⟨⟨i, hi⟩, _⟩ := finset.exists_ne_zero_of_sum_ne_zero (ne_of_eq_of_ne hx.right zero_ne_one.symm),
        rw not_nonempty_iff at h, haveI := h, rw set.range_eq_empty at hi, exact hi } } }
end.

def std_simplex_to_convex_hull (R : Type*) {E : Type*} [linear_ordered_field R]
  [add_comm_group E] [module R E] {ι : Type*} [fintype ι] (v : ι → E)
  : std_simplex R ι → convex_hull R (set.range v) :=
  set.cod_restrict (@set.restrict _ (λ _, E) (std_simplex R ι) (take_linear_combination R v)) _
                   (by { rw ← take_linear_combination_image_of_std_simplex R v,
                         rw ← set.range_restrict (take_linear_combination R v) (std_simplex R ι),
                         exact set.mem_range_self }).

lemma std_simplex_to_convex_hull_cont {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {ι : Type*} [fintype ι] (v : ι → E) : continuous (std_simplex_to_convex_hull ℝ v) :=
begin
  dsimp [std_simplex_to_convex_hull], continuity, apply take_linear_combination_cont
end.

lemma std_simplex_to_convex_hull_surj {E : Type*} [normed_add_comm_group E] [normed_space ℝ E]
  {ι : Type*} [fintype ι] (v : ι → E) : function.surjective (std_simplex_to_convex_hull ℝ v) :=
begin
  convert set.surjective_maps_to_image_restrict (take_linear_combination ℝ v) (std_simplex ℝ ι),
  { symmetry, apply take_linear_combination_image_of_std_simplex },
  { apply function.hfunext rfl, intros x y hxy, cases hxy, cases x with x hx,
    simp [std_simplex_to_convex_hull, set.cod_restrict, set.maps_to.restrict, subtype.map], 
    rw subtype.heq_iff_coe_eq, refl, rw take_linear_combination_image_of_std_simplex, intro, refl }
end

lemma std_simplex_to_convex_hull_is_quot_map {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] {ι : Type*} [fintype ι] (v : ι → E)
  : quotient_map (std_simplex_to_convex_hull ℝ v) :=
  surjection_of_compact_hausdorff_is_quot_map _ (std_simplex_to_convex_hull_surj v)
                                                (std_simplex_to_convex_hull_cont v)

noncomputable
def homeomorph_of_injective_quotient_map {α : Type*} {β : Type*}
  [tα : topological_space α] [tβ : topological_space β] (f : α → β) (hf1 : quotient_map f)
  (hf2 : function.injective f) : α ≃ₜ β :=
begin
  refine equiv.to_homeomorph_of_inducing (equiv.of_bijective f ⟨hf2, hf1.surjective⟩) _,
  have hf : tβ = topological_space.coinduced (equiv.of_bijective f ⟨hf2, hf1.surjective⟩) tα := hf1.right,
  rw inducing_iff, 
  rw ← equiv.coinduced_symm, 
  refine eq.trans _ (eq.symm (congr_arg _ hf)),
  rw coinduced_compose,
  rw equiv.symm_comp_self,
  exact coinduced_id.symm
end

lemma std_simplex_to_convex_hull_eq_affine_combination (R : Type*) {E : Type*}
  [linear_ordered_field R] [add_comm_group E] [module R E] {ι : Type*} [fintype ι] (v : ι → E)
  (x : std_simplex R ι)
  : (std_simplex_to_convex_hull R v x : E) = finset.univ.affine_combination v (x : ι → R) :=
begin
  simp [std_simplex_to_convex_hull, take_linear_combination, finset.affine_combination],
  simp_rw [smul_sub], simp,
  symmetry, convert sub_add_cancel _ _,
  symmetry, rw ← finset.sum_smul, convert one_smul _ _,
  exact x.property.right
end.

lemma affine_basis_coord_take_std_simplex_to_convex_hull {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] {ι : Type*} [fintype ι] (b : affine_basis ι ℝ E)
  (x : std_simplex ℝ ι) (i : ι)
  : b.coord i (std_simplex_to_convex_hull ℝ b.points x) = (x : ι → ℝ) i :=
begin
  convert affine_basis.coord_apply_combination_of_mem b (finset.mem_univ _) x.property.right,
  exact std_simplex_to_convex_hull_eq_affine_combination ℝ b.points x
end

lemma interior_of_convex_hull_of_affine_basis {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] {ι : Type*} [fintype ι] (b : affine_basis ι ℝ E)
  : take_linear_combination ℝ b.points '' (std_simplex ℝ ι \ { p | ∃ i, p i = 0 })
  = interior (convex_hull ℝ (set.range b.points)) :=
begin
  rw interior_convex_hull_aff_basis,
  apply subset_antisymm, 
  { rw set.image_subset_iff,
    rintros x ⟨h1, h2⟩, simp at h2,
    simp, 
    intro i, have := affine_basis_coord_take_std_simplex_to_convex_hull b ⟨x, h1⟩ i,
    dsimp [std_simplex_to_convex_hull] at this, rw this,
    exact lt_of_le_of_ne (h1.left i) (ne.symm (h2 i)) },
  { intros x hx,
    simp at hx,
    have H : (λ i, b.coord i x) ∈ std_simplex ℝ ι,
    { refine ⟨λ i, le_of_lt (hx i), _⟩, simp },
    refine ⟨λ i, b.coord i x, ⟨H, _⟩, _⟩, 
    { simp, intro i, exact ne.symm (ne_of_lt (hx i)) },
    { apply b.ext_elem, intro i,
      convert affine_basis_coord_take_std_simplex_to_convex_hull b ⟨(λ i, b.coord i x), H⟩ i } }
end.

lemma take_linear_combination_bij_on_std_simplex_of_affine_indep {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] {ι : Type*} [fintype ι] (v : ι → E)
  (hv : affine_independent ℝ v)
  : set.bij_on (take_linear_combination ℝ v) (std_simplex ℝ ι) (convex_hull ℝ (set.range v)) :=
begin
  refine ⟨set.maps_to'.mpr (subset_of_eq (take_linear_combination_image_of_std_simplex ℝ v)), _, _⟩,
  { intros x hx y hy hxy,
    rw affine_independent_iff_eq_of_fintype_affine_combination_eq at hv,
    refine hv x y hx.right hy.right _,
    convert hxy; symmetry,
    { exact std_simplex_to_convex_hull_eq_affine_combination ℝ v ⟨x, hx⟩ },
    { exact std_simplex_to_convex_hull_eq_affine_combination ℝ v ⟨y, hy⟩ } },
  { exact subset_of_eq (eq.symm (take_linear_combination_image_of_std_simplex _ _)) }
end

noncomputable
def convex_hull_of_affine_indep_homeo_std_simplex {E : Type*} [normed_add_comm_group E]
  [normed_space ℝ E] {ι : Type*} [fintype ι] (v : ι → E) (hv : affine_independent ℝ v)
  : convex_hull ℝ (set.range v) ≃ₜ std_simplex ℝ ι :=
  homeomorph.symm (homeomorph_of_injective_quotient_map _ (std_simplex_to_convex_hull_is_quot_map v)
                                                        ((set.injective_cod_restrict _).mpr
                                                          ((take_linear_combination_bij_on_std_simplex_of_affine_indep v hv).inj_on.injective)))

lemma set.image_diff_subset_of_inj_on {α β : Type*} {f : α → β} {s t : set α}
  (hst : s ⊆ t) (hf : set.inj_on f t) : f '' (t \ s) = f '' t \ f '' s :=
begin
  refine subset_antisymm _ (set.subset_image_diff f t s),
  rw set.image_subset_iff,
  intros x hx,
  refine ⟨set.mem_image_of_mem _ hx.left, _⟩,
  rintro ⟨y, hy, H⟩, refine hx.right (eq.subst (hf (hst hy) hx.left H) hy)
end

lemma frontier_of_convex_hull_of_affine_basis {E : Type*}
  [normed_add_comm_group E] [normed_space ℝ E] {ι : Type*} [fintype ι] (b : affine_basis ι ℝ E)
  : take_linear_combination ℝ b.points '' (std_simplex ℝ ι ∩ { p | ∃ i, p i = 0 })
  = frontier (convex_hull ℝ (set.range b.points)) :=
begin
  rw frontier_eq_inter_compl_interior,
  rw [interior_compl, compl_compl, is_closed.closure_eq _],
  { rw ← interior_of_convex_hull_of_affine_basis,
    rw ← take_linear_combination_image_of_std_simplex,
    rw ← set.diff_eq_compl_inter,
    rw [← set.image_diff_subset_of_inj_on (set.diff_subset _ _),
        sdiff_sdiff_right_self, set.inf_eq_inter],
    exact (take_linear_combination_bij_on_std_simplex_of_affine_indep b.points b.ind).inj_on },
  { apply set.finite.is_closed_convex_hull, exact set.finite_range _ }
end

lemma span_points_of_insert_zero (k : Type*) {V : Type*} [ring k] [add_comm_group V] [module k V]
  (s : set V) : span_points k (insert (0 : V) s) = submodule.span k s :=
begin
  suffices : vector_span k (insert (0 : V) s) = submodule.span k s,
  { simp [span_points], simp_rw this,
    ext, split; intro h,
    { obtain ⟨v, h1, w, h2, h3⟩ := h, subst h3,
      cases h1, { rw h1, simp, exact h2 },
      { simp, exact submodule.add_mem _ h2 (submodule.subset_span h1) } },
    { exact ⟨0, or.inl rfl, x, h, (add_zero x).symm⟩ } },
  { dsimp [vector_span],
    refine le_antisymm _ (submodule.span_mono _),
    { rw submodule.span_le,
      intros x hx, 
      obtain ⟨v, w, hv, hw, H⟩ := hx, subst H,
      suffices : insert (0 : V) s ⊆ submodule.span k s,
      { exact submodule.sub_mem (submodule.span k s) (this hv) (this hw) },
      rw set.insert_subset,
      exact ⟨(submodule.span k s).zero_mem, submodule.subset_span⟩ },
    { intros x hx, refine ⟨x, 0, set.mem_insert_of_mem _ hx, set.mem_insert 0 s, sub_zero x⟩ } }
end

lemma sphere_homeo_topological_simplex_boundary (n : ℕ)
  : nonempty (metric.sphere (0 : euclidean_space ℝ (fin n)) 1 ≃ₜ topological_simplex_boundary n) := 
begin
  by_cases n = 0,
  { refine eq.mp _ (_ : nonempty ((∅ : set (euclidean_space ℝ (fin n))) ≃ₜ (∅ : set (fin (n + 1) → ℝ)))),
    { suffices : ∅ = metric.sphere (0 : euclidean_space ℝ (fin n)) 1 ∧ ∅ = topological_simplex_boundary n,
      { cases this with h1 h2, congr, exact h1, exact h2, ext, rw h1, ext, rw h2 },
      convert and.intro _ (set.is_empty_coe_sort.mp boundary_of_zero_simplex_empty).symm;
      try { exact congr_arg (λ k, @coe_sort simplex_category Type (concrete_category.has_coe_to_sort simplex_category) (simplex_category.mk k) → ℝ) h },
      symmetry, refine set.eq_empty_of_forall_not_mem _, subst h,
      intro x, dsimp [euclidean_space, pi_Lp] at x, fin_cases x, simp, rw euclidean_space.norm_eq,
      rw finset.univ_eq_empty, simp },
    { refine ⟨⟨⟨(λ x, false.elim x.property), (λ x, false.elim x.property),
               (λ x, false.elim x.property), (λ x, false.elim x.property)⟩, _, _⟩⟩;
      apply continuous_empty_function } },
  suffices : nonempty ((coe : (metric.closed_ball (0 : euclidean_space ℝ (fin n)) 1) → euclidean_space ℝ (fin n)) ⁻¹'
                       metric.sphere 0 1 ≃ₜ topological_simplex_boundary n),
  { obtain ⟨G⟩ := this,
    refine ⟨_⟩,
    refine homeomorph.trans (homeomorph.symm (preim_of_subset_homeo_subset _)) G,
    exact metric.sphere_subset_closed_ball },
  let s := set.range (λ (i j : fin n), ite (i = j) (1 : ℝ) 0) ∪ {0},
  have s_finite : s.finite := set.finite.union (set.finite_range _) (set.finite_singleton _),
  let simplex : set (euclidean_space ℝ (fin n)) := convex_hull ℝ s,
  let b : affine_basis (fin (n + 1)) ℝ (euclidean_space ℝ (fin n))
    := ⟨fin.cons 0 (λ (i j : fin n), ite (i = j) (1 : ℝ) 0), _, _⟩,
  have H : simplex = convex_hull ℝ (set.range b.points),
  { refine congr_arg (convex_hull ℝ) _, rw fin.range_cons, exact set.union_singleton },
  obtain ⟨F, hF⟩ := compact_convex_with_nonempty_interior_homeo_to_ball simplex (convex_convex_hull _ _)  _ _,
  suffices : nonempty ((coe : simplex → euclidean_space ℝ (fin n)) ⁻¹' frontier simplex ≃ₜ topological_simplex_boundary n),
  { obtain ⟨G⟩ := this,
    refine ⟨homeomorph.trans (homeomorph.symm _) G⟩,
    exact homeomorph.trans (embedding_restricts_to_homeomorph _ _ F.embedding) (homeomorph.set_congr hF) },
  suffices : nonempty (frontier simplex ≃ₜ topological_simplex_boundary n),
  { obtain ⟨G⟩ := this,
    refine ⟨homeomorph.trans (preim_of_subset_homeo_subset _) G⟩,
    exact is_closed.frontier_subset (set.finite.is_closed_convex_hull s_finite) },
  suffices : nonempty (frontier (convex_hull ℝ (set.range b.points)) ≃ₜ topological_simplex_boundary n),
  { obtain ⟨G⟩ := this,
    exact ⟨homeomorph.trans (homeomorph.set_congr (congr_arg frontier H)) G⟩ },
  { refine ⟨_⟩,
    let G := convex_hull_of_affine_indep_homeo_std_simplex b.points b.ind,
    refine homeomorph.trans (preim_of_subset_homeo_subset (is_closed.frontier_subset _)).symm
                            (homeomorph.trans _ (preim_of_subset_homeo_subset (set.inter_subset_left _ _))),
    { exact set.finite.is_closed_convex_hull (set.finite_range _) },
    { convert homeomorph.trans (embedding_restricts_to_homeomorph _ G G.embedding) _,
      suffices : G '' (coe ⁻¹' frontier (convex_hull ℝ (set.range b.points)))
               = (coe : std_simplex ℝ (fin (n + 1)) → (fin (n + 1) → ℝ)) ⁻¹' topological_simplex_boundary n,
      { exact homeomorph.set_congr this },
      suffices : G ⁻¹' ((coe : std_simplex ℝ (fin (n + 1)) → (fin (n + 1) → ℝ)) ⁻¹' topological_simplex_boundary n)
               = coe ⁻¹' frontier (convex_hull ℝ (set.range b.points)),
      { refine eq.trans (congr_arg (λ s, G '' s) this.symm) _,
        apply homeomorph.image_preimage },
      rw ← homeomorph.image_symm,
      ext x,
      simp [G, convex_hull_of_affine_indep_homeo_std_simplex, std_simplex_to_convex_hull,
            homeomorph_of_injective_quotient_map, equiv.to_homeomorph_of_inducing],
      have := frontier_of_convex_hull_of_affine_basis b,
      simp [b] at this, rw ← this,
      simp [homeomorph.symm, set.cod_restrict, set.restrict],
      simp_rw [subtype.ext_iff],
      delta topological_simplex_boundary topological_simplex,
      simp, 
      simp_rw [and_assoc, and.left_comm, ← and_assoc],
      simp [simplex_category.to_Top'_obj, simplex_category.mk],
      refine eq.to_iff _, congr, ext : 1,
      congr' 1,
      rw [and.comm],
      congr' 1, 
      exact propext (and_self _) } },
  { rw [H, ← interior_of_convex_hull_of_affine_basis, set.nonempty_image_iff],
    refine ⟨(barycenter n).val, (barycenter n).property, _⟩,
    simp [barycenter], norm_cast, exact nat.succ_ne_zero n },
  { rw [H, ← take_linear_combination_image_of_std_simplex],
    exact (compact_std_simplex (fin (n + 1))).image (take_linear_combination_cont _) },
  { refine (affine_independent_iff_linear_independent_vsub ℝ _ 0).mpr _,
    convert linear_independent.comp (basis.linear_independent (pi.basis_fun ℝ (fin n)))
                                    (λ (i : {x : fin (n + 1) // x ≠ 0}), fin.pred i.val i.property) _,
    { ext i, cases i with i hi, simp,
      cases i with i hi', cases i, exfalso, exact hi rfl,
      have : fin.succ ⟨i, nat.lt_of_succ_lt_succ hi'⟩ = ⟨i.succ, hi'⟩ :=
        fin.succ_mk n i (nat.lt_of_succ_lt_succ hi'), 
      simp_rw ← this, rw fin.cons_succ, cases x with j hj,
      split_ifs with h'; simp at h',
      { symmetry, convert linear_map.std_basis_same ℝ (λ _, ℝ) _ _, simp [fin.pred], exact h' },
      { symmetry, convert linear_map.std_basis_ne ℝ (λ _, ℝ) _ _ _ _, simp [fin.pred], exact ne.symm h' } },
    { rintros ⟨i, hi⟩ ⟨j, hj⟩ H, simp at H ⊢, exact H } },
  { rw [eq_top_iff, fin.range_cons],
    rw [affine_subspace.le_def, affine_subspace.top_coe, coe_affine_span,
        span_points_of_insert_zero],
    rw [← @submodule.top_coe ℝ (euclidean_space ℝ (fin n)), set_like.coe_subset_coe, ← eq_top_iff],
    exact (pi.basis_fun ℝ (fin n)).span_eq }
end.

lemma zeroth_homology_of_zero_sphere {R : Type*} [comm_ring R] [nontrivial R]
  : is_isomorphic ((singular_homology R 0).obj (Top.of (metric.sphere (0 : euclidean_space ℝ (fin 1)) 1)))
                  ((Module.free R).obj (fin 2)) :=
begin
  obtain ⟨G⟩ := sphere_homeo_topological_simplex_boundary 1,
  exact ⟨(singular_homology R 0).map_iso (@Top.iso_of_homeo (Top.of (metric.sphere (0 : euclidean_space ℝ (fin 1)) 1)) 
                                                            (Top.of (topological_simplex_boundary 1)) G)
         ≪≫ zeroth_homology_of_boundary_of_one_simplex⟩
end

lemma nth_homology_of_n_sphere {R : Type*} [comm_ring R] [nontrivial R] (n : ℕ) (hn : n > 0)
  : is_isomorphic ((singular_homology R n).obj (Top.of (metric.sphere (0 : euclidean_space ℝ (fin (n + 1))) 1)))
                  (Module.of R R) :=
begin
  obtain ⟨G⟩ := sphere_homeo_topological_simplex_boundary (n + 1),
  exact ⟨(singular_homology R n).map_iso (@Top.iso_of_homeo (Top.of (metric.sphere (0 : euclidean_space ℝ (fin (n + 1))) 1)) 
                                                            (Top.of (topological_simplex_boundary (n + 1))) G)
         ≪≫ nth_homology_of_boundary_of_n_plus_one_simplex n hn⟩
end