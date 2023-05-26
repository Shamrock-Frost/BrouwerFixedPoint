import topology.constructions
import topology.separation
import topology.category.Top.basic
import topology.homotopy.basic
import analysis.convex.topology

lemma quotient_map_of_is_closed_map {α β} [topological_space α] [topological_space β] 
  (f : α → β) : function.surjective f → is_closed_map f → continuous f → quotient_map f :=
begin
  intros hS hC hCont,
  rw quotient_map_iff,
  split, assumption,
  intro U, 
  rw [← is_closed_compl_iff, ← is_closed_compl_iff, ← set.preimage_compl],
  generalize : Uᶜ = C, clear U,
  split, 
  { apply is_closed.preimage, assumption },
  { intro h, rw (_ : C = f '' (f ⁻¹' C)),
    { apply hC, assumption },
    { symmetry, apply set.image_preimage_eq_of_subset,
      rw hS.range_eq, apply set.subset_univ } }
end

lemma surjection_of_compact_hausdorff_is_quot_map {α β} [topological_space α] [topological_space β]
  [compact_space α] [t2_space β]
  (f : α → β) : function.surjective f → continuous f → quotient_map f :=
λ hSurj hCont, quotient_map_of_is_closed_map f hSurj hCont.is_closed_map hCont

noncomputable
def lift_along_quot_map {α β γ : Top} (q : α ⟶ β) (f : α ⟶ γ) (Hquot : quotient_map q)
  (H : ∀ x y, q x = q y → f x = f y) : β ⟶ γ := {
    to_fun := λ b, f (classical.some (Hquot.left b)),
    continuous_to_fun := (quotient_map.continuous_iff Hquot).mpr
                          (continuous.congr f.continuous_to_fun
                            (λ x, H x _ (eq.symm (classical.some_spec (Hquot.left (q x))))))
  }

lemma lift_along_quot_map_spec {α β γ : Top} (q : α ⟶ β) (f : α ⟶ γ) (Hquot : quotient_map q)
  (H : ∀ x y, q x = q y → f x = f y) (b : β) (a : α) (h : q a = b)
  : lift_along_quot_map q f Hquot H b = f a := 
  H (classical.some (lift_along_quot_map._proof_1 q Hquot b)) a
    ((classical.some_spec (Hquot.left b)).trans h.symm)

lemma lift_along_quot_map_comm_square
  {α β γ δ : Top} (q : α ⟶ β)
  (f : α ⟶ γ) (g : γ ⟶ δ)
  (Hquot : quotient_map q)
  (H : ∀ x y, q x = q y → f x = f y)
  : lift_along_quot_map q f Hquot H ≫ g
  = lift_along_quot_map q (f ≫ g) Hquot (λ x y Hxy, (congr_arg g (H x y Hxy) : g (f x) = g (f y))) := 
begin
  ext b, obtain ⟨a, ha⟩ := Hquot.left b,
  symmetry,
  refine eq.trans (lift_along_quot_map_spec q (f ≫ g) Hquot _ b a ha) _,
  symmetry, exact congr_arg g (lift_along_quot_map_spec q f Hquot H b a ha)
end

universe u
def cylinder : Top.{u} ⥤ Top.{u} := {
  obj := λ X, Top.of (unit_interval × X),
  map := λ X Y f, (continuous_map.id _).prod_map f,
  map_id' := by { intros, ext1 ⟨x, y⟩, refl },
  map_comp' := by { intros, ext1 ⟨x, y⟩, refl },
}

def homeomorph.subtype_pi_homeomorph_pi
  {α : Type*} {β : α → Type*} {P : Π (a : α), β a → Prop}
  [τ : Π (a : α), topological_space (β a)]
  : { f : Π (a : α), β a // ∀ a, P a (f a) } ≃ₜ (Π (a : α), { b // P a b }) :=
  equiv.subtype_pi_equiv_pi.to_homeomorph_of_inducing
    ⟨by { simp only [subtype.topological_space, Pi.topological_space,
                     induced_compose, induced_infi],
          refl }⟩

def homeomorph.subtype_prod_equiv_prod
  {α : Type*} {β : Type*} {p : α → Prop} {q : β → Prop} 
  [tα : topological_space α] [tβ : topological_space β]
  : {c : α × β // p c.fst ∧ q c.snd} ≃ₜ {a // p a} × {b // q b} :=
  equiv.subtype_prod_equiv_prod.to_homeomorph_of_inducing
    ⟨by { simp only [subtype.topological_space, prod.topological_space,
                    induced_inf, induced_compose],
          refl }⟩

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_add E] [has_continuous_smul ℝ E] {s : set E} {x : E}

/-- A non-empty star convex set is a contractible space. -/
def star_convex.contraction (x : s) (h : star_convex ℝ (x : E)  s) :
  (continuous_map.id s).homotopy (continuous_map.const s x) := {
  to_fun := λ p, ⟨p.1.1 • x + (1 - p.1.1) • p.2,
                    h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel'_right _ _)⟩,
  map_zero_left' := λ _, by simp only [subtype.val_eq_coe, set.Icc.coe_zero,
                                       zero_smul, tsub_zero, subtype.coe_eta,
                                       continuous_map.id_apply, one_smul, zero_add],
  map_one_left' := λ _, by simp only [subtype.val_eq_coe, set.Icc.coe_one, one_smul,
                                      sub_self, zero_smul, add_zero, subtype.coe_eta,
                                      continuous_map.const_apply]
}

/-- A non-empty convex set is a contractible space. -/
def convex.contraction (hs : convex ℝ s) (x0 : s) :
  (continuous_map.id s).homotopy (continuous_map.const s x0) :=
(hs.star_convex x0.coe_prop).contraction x0

noncomputable
def embedding.pullback {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] {f : α → β} (hf : embedding f) (g : C(γ, β))
  (hg : set.range g ⊆ set.range f) : C(γ, α) := {
    to_fun := λ x, classical.some (hg (set.mem_range_self x)),
    continuous_to_fun := by {
      refine hf.continuous_iff.mpr _,
      apply continuous.congr g.continuous_to_fun,
      intro x, symmetry, exact classical.some_spec (hg (set.mem_range_self x))
    }
  }

lemma embedding.pullback_spec {α β γ : Type*} [topological_space α] [topological_space β]
  [topological_space γ] {f : α → β} (hf : embedding f) (g : C(γ, β))
  (hg : set.range g ⊆ set.range f) : ∀ x, f (hf.pullback g hg x) = g x :=
begin
  intro x, exact classical.some_spec (hg (set.mem_range_self x))
end

noncomputable def embedding_restricts_to_homeomorph {X Y : Type*} [topological_space X]
  [topological_space Y] (s : set X) (f : X → Y) (hf : embedding f) : s ≃ₜ f '' s :=
(homeomorph.of_embedding _ (hf.comp embedding_subtype_coe)).trans $ homeomorph.set_congr $
  (set.image_eq_range _ _).symm

theorem function.eq_of_sigma_mk_comp {α ι : Type*} {π : ι → Type*} [nonempty α]
  {i j : ι} {f : α → π i} {g : α → π j} (h : sigma.mk i ∘ f = sigma.mk j ∘ g) :
  i = j ∧ f == g :=
begin
  inhabit α,
  obtain ⟨rfl, -⟩ : i = j ∧ f default == g default, by simpa only [(∘)] using congr_fun h default,
  simpa [function.funext_iff] using h
end

/-- A continuous map from a connected space to a `Σ`-type can be lifted to one of the
components `π i`. -/
theorem continuous.exists_lift_sigma {X ι : Type*} {π : ι → Type*} [topological_space X]
  [connected_space X] [∀ i, topological_space (π i)] {f : X → Σ i, π i} (hf : continuous f) :
  ∃ (i : ι) (g : X → π i), continuous g ∧ f = sigma.mk i ∘ g :=
begin
  rcases sigma.is_connected_iff.1 (is_connected_range hf) with ⟨i, s, -, hs⟩,
  choose g hgs hgf using set.range_subset_iff.1 hs.subset,
  obtain rfl : f = sigma.mk i ∘ g := (funext hgf).symm,
  refine ⟨i, g, _, rfl⟩,
  rwa [← embedding_sigma_mk.continuous_iff] at hf
end

/-- A continuous map from a connected space to a `Σ`-type can be lifted to one of the
components `π i`. -/
theorem continuous_map.exists_lift_sigma {X ι : Type*} {π : ι → Type*} [topological_space X]
  [connected_space X] [∀ i, topological_space (π i)] (f : C(X, Σ i, π i)) :
  ∃ (i : ι) (g : C(X, π i)), f = continuous_map.comp ⟨sigma.mk i⟩ g :=
let ⟨i, g, hgc, hfg⟩ := f.continuous.exists_lift_sigma in
⟨i, ⟨g, hgc⟩, fun_like.ext' hfg⟩

noncomputable def equiv.continuous_map_sigma_equiv {X ι : Type*} {π : ι → Type*}
  [topological_space X] [connected_space X] [∀ i, topological_space (π i)] :
  C(X, Σ i, π i) ≃ Σ i, C(X, π i) :=
equiv.symm $ equiv.of_bijective (λ g, continuous_map.comp ⟨sigma.mk g.1⟩ g.2) $
  begin
    refine ⟨_, λ f, let ⟨i, g, h⟩ := f.exists_lift_sigma in ⟨⟨i, g⟩, h.symm⟩⟩,
    rintro ⟨i, g⟩ ⟨j, g'⟩ h,
    obtain ⟨rfl : i = j, h⟩ := function.eq_of_sigma_mk_comp (fun_like.ext'_iff.1 h),
    simpa using h
  end
