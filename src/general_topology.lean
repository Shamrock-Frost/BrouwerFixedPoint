import topology.constructions
import topology.separation
import topology.category.Top.basic
import topology.homotopy.basic
import analysis.convex.star

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
λ hSurj hCont, quotient_map_of_is_closed_map f hSurj
                                             (λ C hC, (hC.is_compact.image hCont).is_closed)
                                             hCont

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
noncomputable
def cylinder : Top.{u} ⥤ Top.{u} := {
  obj := λ X, Top.of (unit_interval × X),
  map := λ X Y f, continuous_map.mk (λ p : unit_interval × X, (p.fst, f p.snd))
                                    (continuous.prod_mk continuous_fst
                                      (continuous.comp f.continuous continuous_snd)),
  map_id' := by { intros, ext p, cases p, simp, refl },
  map_comp' := by { intros, ext p, cases p, simp, refl },
}

def homeomorph.Pi_to_subtype
  {α : Type*} {β : α → Type*} {P : Π (a : α), β a → Prop}
  [τ : Π (a : α), topological_space (β a)]
  : { f : Π (a : α), β a // ∀ a, P a (f a) } ≃ₜ (Π (a : α), { b // P a b }) :=
  equiv.subtype_pi_equiv_pi.to_homeomorph_of_inducing
    ⟨by { simp [subtype.topological_space, Pi.topological_space, induced_compose], refl }⟩

def homeomorph.subtype_prod_equiv_prod
  {α : Type*} {β : Type*} {p : α → Prop} {q : β → Prop} 
  [tα : topological_space α] [tβ : topological_space β]
  : {c : α × β // p c.fst ∧ q c.snd} ≃ₜ {a // p a} × {b // q b} :=
  equiv.subtype_prod_equiv_prod.to_homeomorph_of_inducing
    ⟨by { simp [subtype.topological_space, prod.topological_space, induced_inf, induced_compose],
          refl }⟩

variables {E : Type*} [add_comm_group E] [module ℝ E] [topological_space E]
  [has_continuous_add E] [has_continuous_smul ℝ E] {s : set E} {x : E}

/-- A non-empty star convex set is a contractible space. -/
def star_convex.contraction (h : star_convex ℝ x s) (h' : s.nonempty) :
  (continuous_map.id s).homotopy
    (continuous_map.const s ⟨x, star_convex.mem h h'⟩) := {
    to_fun := λ p, ⟨p.1.1 • x + (1 - p.1.1) • p.2,
                    h p.2.2 p.1.2.1 (sub_nonneg.2 p.1.2.2) (add_sub_cancel'_right _ _)⟩,
    map_zero_left' := λ _, by simp,
    map_one_left' := λ _, by simp,
  }

/-- A non-empty convex set is a contractible space. -/
noncomputable
lemma convex.contraction (hs : convex ℝ s)
  : Π (x0 : s), (continuous_map.id s).homotopy (continuous_map.const s x0)
| ⟨x0, h⟩ := (hs.star_convex h).contraction ⟨x0, h⟩