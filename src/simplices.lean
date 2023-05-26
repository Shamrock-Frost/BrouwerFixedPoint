import algebraic_topology.simplex_category
import algebraic_topology.simplicial_object
import analysis.convex.topology
import algebraic_topology.simplicial_set
import category_theory.natural_isomorphism
import topology.category.Top.limits.products
import .category_theory .general_topology

local attribute [instance]
  category_theory.concrete_category.has_coe_to_sort
  category_theory.concrete_category.has_coe_to_fun

noncomputable theory

namespace simplex_category

def squash (n : ℕ) : simplex_category.mk n ⟶ simplex_category.mk 0 :=
  simplex_category.mk_hom ⟨(λ _, 0), by { intros x y _, reflexivity }⟩

def to_Top'_obj (x : simplex_category) := std_simplex ℝ x

open_locale simplicial big_operators classical

instance (x : simplex_category) : has_coe_to_fun x.to_Top'_obj (λ _, x → ℝ) :=
⟨λ f, (f : x → ℝ)⟩

lemma to_Top'_obj_coord_sum_nonzero {x : simplex_category} {s : finset x}
  (p : x.to_Top'_obj) : 0 ≤ ∑ i in s, p i := 
  le_of_eq_of_le (finset.sum_eq_zero (λ _ _, rfl)).symm
                 (finset.sum_le_sum (λ i _, p.property.left i))

@[ext]
lemma to_Top'_obj.ext {x : simplex_category} (f g : x.to_Top'_obj) :
  (f : x → ℝ) = g → f = g := subtype.ext

-- Should be defined in analysis.convex.basic, maybe?
def to_Top'_map {x y : simplex_category} (f : x ⟶ y)
  : x.to_Top'_obj → y.to_Top'_obj :=
    λ p, ⟨λ i, ∑ j in (finset.univ.filter (λ k, f k = i)), p j,
          λ i, to_Top'_obj_coord_sum_nonzero p,
          by { refine eq.trans _ p.2.right,
                refine eq.trans (finset.sum_bUnion _).symm _,
                { refine finset.pairwise_disjoint_coe.mp _,
                  convert set.pairwise_disjoint_fiber f _,
                  ext, simp },
                { apply finset.sum_congr,
                  { rw finset.eq_univ_iff_forall,
                    intro i,
                    rw finset.mem_bUnion,
                    exact ⟨f i, by simp, by simp⟩ },
                  { intros, refl } } }⟩

@[simp]
lemma coe_to_Top'_map {x y : simplex_category} (f : x ⟶ y) (g : x.to_Top'_obj) (i : y) :
  to_Top'_map f g i = ∑ j in (finset.univ.filter (λ k, f k = i)), g j := rfl

@[continuity]
lemma continuous_to_Top'_map {x y : simplex_category} (f : x ⟶ y) :
  continuous (to_Top'_map f) :=
continuous.subtype_mk (continuous_pi $ λ i, continuous_finset_sum _ $
  λ j hj, continuous.comp (continuous_apply _) continuous_subtype_val) _

@[simps]
def to_Top' : simplex_category ⥤ Top :=
{ obj := λ x, Top.of x.to_Top'_obj,
  map := λ x y f, ⟨to_Top'_map f⟩,
  map_id' := begin
    intros x,
    ext f i : 3,
    change (finset.univ.filter (λ k, k = i)).sum _ = _,
    simp [finset.sum_filter]
  end,
  map_comp' := begin
    intros x y z f g,
    ext h i : 3,
    dsimp,
    erw ← finset.sum_bUnion,
    apply finset.sum_congr,
    { exact finset.ext (λ j, ⟨λ hj, by simpa using hj, λ hj, by simpa using hj⟩) },
    { tauto },
    { refine finset.pairwise_disjoint_coe.mp _,
      convert set.pairwise_disjoint_fiber f _,
      ext, simp },
  end }.

def topological_simplex_alt_desc (n : simplex_category)
  : {f : n → nnreal | ∑ (i : n), f i = 1} ≃ₜ std_simplex ℝ n := {
  to_fun := λ x, ⟨λ i, (x.val i).val, λ i, (x.val i).property,
                    by { have := (congr_arg subtype.val x.property),
                        refine eq.trans _ this,
                        symmetry, 
                        simp at this,
                        have := map_sum (⟨subtype.val, _, _⟩ : nnreal →+ ℝ) x.val finset.univ,
                        swap, { refl }, swap, { rintros ⟨x, _⟩ ⟨y, _⟩, simp },
                        refine eq.trans this _,
                        congr }⟩,
  inv_fun := λ x, ⟨λ i, ⟨x.val i, x.property.left i⟩,
                     by { refine subtype.eq _,
                         have := x.property.right,
                         refine eq.trans _ this,
                         let f : fin (n.len + 1) → nnreal := λ i, ⟨x.val i, x.property.left i⟩,
                         have := map_sum (⟨subtype.val, _, _⟩ : nnreal →+ ℝ) f finset.univ,
                         swap, { refl }, swap, { rintros ⟨x, _⟩ ⟨y, _⟩, simp },
                         refine eq.trans this _,
                         congr }⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, by simp,
  continuous_to_fun := by { simp, continuity,
                            apply continuous.congr ((continuous_apply i).comp continuous_subtype_coe), 
                            simp },
  continuous_inv_fun := by { simp, continuity,
                             apply continuous.congr ((continuous_apply i).comp continuous_subtype_coe), 
                             simp }
}.

def to_Top_iso_to_Top' : to_Top ≅ to_Top' := 
  category_theory.nat_iso.of_components (λ x, Top.iso_of_homeo (topological_simplex_alt_desc x))
    (by { intros n m f,
          ext p k, 
          change ((finset.filter (λ j, f j = k) finset.univ).sum p.val).val
               = (finset.filter (λ j, f j = k) finset.univ).sum (λ i, (p.val i).val),
          exact map_sum (⟨subtype.val, rfl, nnreal.coe_add⟩ : nnreal →+ ℝ) p.val _, })

end simplex_category

open category_theory

def Top.to_sSet' : Top ⥤ sSet :=
colimit_adj.restricted_yoneda simplex_category.to_Top'

def Top.to_sSet_iso_to_sSet' : Top.to_sSet ≅ Top.to_sSet' :=
begin
  refine @functor.map_iso _ _ _ _
    (@restricted_yoneda_functor simplex_category _ Top.{0} _)
    (opposite.op simplex_category.to_Top) (opposite.op simplex_category.to_Top')
    (iso.op simplex_category.to_Top_iso_to_Top'.symm),
end

lemma ext_to_hext {α : Type*} {β γ : α → Type*} (f : Π {a : α}, β a → γ a)
  (e : ∀ {a} (x y : β a), x = y ↔ f x = f y)
  {a a' : α} (x : β a) (y : β a') : a = a' → (x == y ↔ f x == f y) :=
begin
  intro h, induction h,
  rw [heq_iff_eq, heq_iff_eq], apply e,
end

/-
β = Σ j, (f j).α

x : C ↦ C(F.obj x, β)
y : Cᵒᵖ ⥤ Type

z : 
-/

universes u u'
def connected_functor_preserves_coprod {C : Type (max u u')} [small_category C]
  (F : C ⥤ Top.{max u u'}) {J : Type u'} (f : J → Top.{max u u'})
  (hF : ∀ x : C, connected_space (F.obj x))
  : limits.preserves_colimit (discrete.functor f) (colimit_adj.restricted_yoneda F) :=
begin
  apply limits.preserves_colimit_of_preserves_colimit_cocone (Top.sigma_cofan_is_colimit.{(max u u') u'} f),
  apply limits.evaluation_jointly_reflects_colimits,
  intro x,
  let α := functor.associator (discrete.functor f) (colimit_adj.restricted_yoneda F)
                              ((evaluation Cᵒᵖ (Type (max u u'))).obj x),  
  refine limits.is_colimit.equiv_of_nat_iso_of_iso α.symm _ _
           (functor.map_cocone_map_cocone' _ _ _ _) _,
  change limits.is_colimit ((coyoneda.obj (F.op.obj x)).map_cocone (Top.sigma_cofan.{(max u u') u'} f)),
  dsimp [Top.sigma_cofan, coyoneda, functor.map_cocone, limits.cocones.functoriality],
  let e : (F.obj x.unop ⟶ Top.of (Σ i, f i)) ≃ Σ i, F.obj x.unop ⟶ f i :=
    equiv.continuous_map_sigma_equiv,
  refine ⟨_, _, _⟩,
  { exact λ s g, s.ι.app ⟨(e g).1⟩ (e g).2 },
  { rintro c ⟨j⟩,
    ext g,
    dsimp at g ⊢,
    set φ : (Σ j, F.obj x.unop ⟶ f j) → c.X := λ g, c.ι.app ⟨g.1⟩ g.2,
    change φ (e (e.symm ⟨j, g⟩)) = φ ⟨j, g⟩,
    rw [e.apply_symm_apply] },
  { intros c m h', ext g,
    rw [← h'],
    exact congr_arg m (e.symm_apply_apply g).symm }
end

def topological_simplex (n : ℕ) := simplex_category.to_Top'_obj (simplex_category.mk n)

def topological_simplex.point : topological_simplex 0 := ⟨(λ _, 1), by {
  split, { intro, exact zero_le_one },
  apply finset.sum_eq_single_of_mem,
  exact finset.mem_univ 0,
  intros b h h', cases b with b bh, 
  exfalso, cases b, trivial, simp at bh, 
  assumption
}⟩

instance topological_simplex.point_unique : unique (topological_simplex 0) := {
  default := topological_simplex.point,
  uniq := by {
    suffices : ∀ x : topological_simplex 0, x.val 0 = 1,
    { intro, ext x,
      cases x with k hk, simp at hk, subst hk,
      exact eq.trans (this a) (this topological_simplex.point).symm },
    rintro ⟨f, h⟩,
    exact eq.trans finset.sum_singleton.symm h.right }
}

noncomputable
def inclusion (n : ℕ) : Top.of (topological_simplex n) ⟶ Top.of (topological_simplex (n + 1)) := 
  simplex_category.to_Top'.map (simplex_category.δ 0)

noncomputable
def const_vertex (n : ℕ) (i : simplex_category.mk (n + 1))
  : Top.of (topological_simplex n) ⟶ Top.of (topological_simplex (n + 1)) :=
  simplex_category.to_Top'.map (simplex_category.squash n
                               ≫ simplex_category.const (simplex_category.mk (n+1)) i)

noncomputable
def vertex (n : ℕ) (i : simplex_category.mk n) : topological_simplex n 
  := simplex_category.to_Top'.map (simplex_category.const (simplex_category.mk n) i)
                                  topological_simplex.point

instance Top.to_sSet'_preserves_coprod {J : Type} (f : J → Top)
  : limits.preserves_colimit (discrete.functor f) Top.to_sSet' :=
begin 
  apply connected_functor_preserves_coprod,
  intro x,
  -- todo: why do we need this?
  haveI : has_continuous_smul ℝ (fin (x.len + 1) → ℝ) := @pi.has_continuous_smul _ _ _ _ _ _
    (λ _, infer_instance),
  refine (subtype.connected_space ((convex_std_simplex ℝ (fin (x.len + 1))).is_connected _)),
  rw ← set.nonempty_coe_sort, constructor,
  exact vertex x.len 0, 
end

lemma topological_simplex.coord_le_one (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) : x.val i ≤ 1 :=
begin
  transitivity (finset.univ.sum x.val),
  { rw ← finset.insert_erase (finset.mem_univ i),
    rw finset.sum_insert (finset.not_mem_erase _ _),
    refine le_of_eq_of_le (add_zero _).symm _,
    apply add_le_add, refl,
    apply simplex_category.to_Top'_obj_coord_sum_nonzero },
  { exact le_of_eq x.property.right }
end

lemma topological_simplex.has_one_implies_eq_zero (n : ℕ) (i : simplex_category.mk n)
  (x : topological_simplex n) (h : x.val i = 1) : ∀ j, i ≠ j → x.val j = 0 :=
begin
  intros j hij,
  have : finset.sum (insert i (insert j (finset.erase (finset.erase finset.univ i) j))) x.val = 1,
  { rw ← x.property.right, congr, rw [finset.insert_erase, finset.insert_erase],
    apply finset.mem_univ,
    apply finset.mem_erase_of_ne_of_mem,
    symmetry, assumption,
    apply finset.mem_univ },
  rw [finset.sum_insert, finset.sum_insert] at this,
  { rw h at this,
    rw add_right_eq_self at this,
    refine le_antisymm _ (x.property.left j),
    refine le_of_le_of_eq _ this,
    refine le_add_of_nonneg_right _,
    apply simplex_category.to_Top'_obj_coord_sum_nonzero },
  simp, simp, assumption
end

lemma vertex_coord_one (n : ℕ) (i : simplex_category.mk n) : 
  @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) i = 1 := 
begin
  simp [vertex],
  transitivity finset.univ.sum (λ _, (1 : ℝ)),
  congr, 
  { refine finset.eq_univ_of_forall _, intro x, simp, refl },
  { norm_num }
end

lemma vertex_coord_zero (n : ℕ) (i j : simplex_category.mk n) (h : i ≠ j) :
  @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) j = 0 :=
topological_simplex.has_one_implies_eq_zero n i _ (vertex_coord_one n i) j h

lemma eq_vertex (n : ℕ) (i : simplex_category.mk n) (x : topological_simplex n)
  : x.val i = 1 → x = vertex n i :=
begin
  intros hi,
  ext k,
  by_cases (i = k),
  { subst h, rw vertex_coord_one, rw ← hi, refl },
  { rw vertex_coord_zero n _ _ h,
    exact topological_simplex.has_one_implies_eq_zero n i x hi _ h }
end

lemma vertex_coord_binary (n : ℕ) (i j : simplex_category.mk n) : 
  @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) j = 0
  ∨ @coe_fn _ _ (simplex_category.to_Top'_obj.has_coe_to_fun (simplex_category.mk n))
              (vertex n i) j = 1 := 
begin
  by_cases (i = j),
  { subst h, right, apply vertex_coord_one },
  { left, apply vertex_coord_zero, assumption }
end

lemma const_desc (n : ℕ) (i : simplex_category.mk (n + 1)) (x : topological_simplex n)
  : const_vertex n i x = vertex (n+1) i :=
begin
  delta const_vertex,
  delta vertex,
  rw simplex_category.to_Top'.map_comp,
  simp, congr,
  apply @unique.eq_default _ topological_simplex.point_unique
end

lemma deg_zero_zeroth_coface_map_is_vertex_one 
  : simplex_category.to_Top'_map (simplex_category.δ 0) topological_simplex.point
  = vertex 1 1 :=
by {
  transitivity const_vertex 0 1 topological_simplex.point,
  { congr, ext, cases x with x hx, cases x,
    refl, exfalso, simp at hx, assumption },
  { apply const_desc } 
}

lemma deg_zero_oneth_coface_map_is_vertex_zero
  : simplex_category.to_Top'_map (simplex_category.δ 1) topological_simplex.point
  = vertex 1 0 :=
by {
  transitivity const_vertex 0 0 topological_simplex.point,
  { congr, ext, cases x with x hx, cases x,
    refl, exfalso, simp at hx, assumption },
  { apply const_desc } 
}

def one_simplex_homeo_interval : topological_simplex 1 ≃ₜ unit_interval := {
  to_fun := λ p, ⟨p.val 0, p.property.left 0, topological_simplex.coord_le_one 1 0 p⟩,
  inv_fun := λ t, ⟨(λ i, if i = 0 then t else unit_interval.symm t),
                   by { intro x, change 0 ≤ ite (x = 0) (t : ℝ) (unit_interval.symm t),
                        split_ifs; exact unit_interval.nonneg _ }, 
                   by { rw finset.univ_fin2, simp }⟩,
  left_inv := by { intro p, ext i, dsimp, fin_cases i,
                   { change ite (0 = 0) (p.val 0) (1 - p.val 0) = p.val 0, simp },
                   { dsimp [coe_fn, has_coe_to_fun.coe],
                     split_ifs, exfalso, cases h,
                     rw sub_eq_iff_eq_add, symmetry, rw add_comm,
                     convert p.property.right,
                     simp [list.pmap], congr, } },
  right_inv := by { intro t, ext, simp },
  continuous_to_fun := by { continuity,
                            exact (continuous_apply (0 : fin 2)).comp continuous_subtype_val },
  continuous_inv_fun := by { continuity, apply continuous.if_const, continuity }
}.

lemma coface_map_misses_output (n : ℕ) (i : fin (n + 2)) (j : simplex_category.mk n) :
  simplex_category.δ i j ≠ i :=
  fin.succ_above_ne i j

lemma succ_sigma_of_nonzero (n : ℕ) (k : simplex_category.mk (n + 1)) (h : k ≠ 0) 
  : fin.succ (simplex_category.σ 0 k) = k :=
begin
  cases k with k hk,
  cases k, contradiction, refl
end

lemma fourth_simplicial_identity_modified (n : ℕ)
  (j : fin (n + 2)) (i : simplex_category.mk (n + 1))
  (H : ¬ (j = 0 ∧ i = 0))
  : simplex_category.δ j (simplex_category.σ 0 i)
  = simplex_category.σ 0 (simplex_category.δ j.succ i) :=
begin
  by_cases j = 0,
  { subst h, rw not_and at H, specialize H rfl,
    have : i = simplex_category.δ 0 (simplex_category.σ 0 i),
    { symmetry, apply succ_sigma_of_nonzero, assumption },
    rw this,
    generalize : simplex_category.σ 0 i = i', clear H this i,
    transitivity simplex_category.δ 0
                    ((simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) i'),
    refl,
    rw simplex_category.δ_comp_σ_self, 
    transitivity (simplex_category.δ (fin.succ 0) ≫ simplex_category.σ 0)
                    (simplex_category.δ 0 i'),
    rw simplex_category.δ_comp_σ_succ, refl, refl },
  { transitivity (simplex_category.σ 0 ≫ simplex_category.δ j) i, refl,
    rw ← simplex_category.δ_comp_σ_of_gt, 
    { refl },
    { apply lt_of_le_of_ne,
      apply fin.zero_le,
      apply ne.symm, dsimp,
      assumption } }
end

lemma sum_over_n_simplices_eq {G} [add_comm_monoid  G] (n : ℕ) (f : simplex_category.mk n → G) :
  finset.univ.sum f = (finset.filter (λ i : simplex_category.mk (n + 1), i ≠ 0) finset.univ).sum
                                     (λ j, f (simplex_category.σ 0 j)) :=
@finset.sum_bij' G (simplex_category.mk n) (simplex_category.mk (n + 1)) _
                 finset.univ
                 (finset.filter (λ i : simplex_category.mk (n + 1), i ≠ 0) finset.univ)
                 f
                 (λ i, f (simplex_category.σ 0 i))
                 (λ i _, simplex_category.δ 0 i) 
                 (λ x h, finset.mem_filter.mpr ⟨finset.mem_univ _, coface_map_misses_output n 0 x⟩)
                 (λ x h, congr_arg f (by {
                   transitivity (simplex_category.δ (fin.cast_succ 0) ≫ simplex_category.σ 0) x,
                   { rw simplex_category.δ_comp_σ_self, refl },
                   { refl } }))
                 (λ j _, simplex_category.σ 0 j)
                 (λ j _, finset.mem_univ _)
                 (λ i h, by { transitivity (simplex_category.δ (fin.cast_succ 0)
                                            ≫ simplex_category.σ 0) i,
                              refl,
                              rw simplex_category.δ_comp_σ_self, refl })
                 (λ j h, by { dsimp,
                              simp at h,
                              exact succ_sigma_of_nonzero n j h })
