import LTE_port.ab4
import algebra.category.Module.colimits
import LTE_port.AddCommGroup.ab4

open category_theory
open category_theory.limits

local attribute [instance] category_theory.limits.has_zero_object.has_zero

universes v'' v' v u'' u' u 

open_locale classical

instance Module.forget₂_AddCommGroup_preserves_zero_morphisms {R : Type*} [ring R]
  : (forget₂ (Module R) AddCommGroup).preserves_zero_morphisms := ⟨⟩

instance Module.forget₂_AddCommGroup_faithful {R : Type*} [ring R]
  : faithful (forget₂ (Module R) AddCommGroup) :=
begin
  refine ⟨_⟩,
  intros X Y f g H,
  ext x, 
  rw [← linear_map.to_add_monoid_hom_coe, ← linear_map.to_add_monoid_hom_coe],
  exact congr_arg2 _ H (refl x)
end.

noncomputable
instance Module.forget₂_AddCommGroup_reflects_exact_sequences {R : Type*} [ring R]
  : functor.reflects_exact_sequences (forget₂ (Module R) AddCommGroup) := 
begin
  apply functor.reflects_exact_sequences_of_preserves_zero_morphisms_of_faithful
end

instance Module.forget₂_AddCommGroup_reflects_mono {R : Type*} [ring R]
  : functor.reflects_monomorphisms (forget₂ (Module R) AddCommGroup) := by apply_instance

instance Module.forget₂_AddCommGroup_preserves_mono {R : Type*} [ring R]
  : functor.preserves_monomorphisms (forget₂ (Module R) AddCommGroup) := by apply_instance

instance coextension.module_structure (R : Type*) [ring R] (G : Type*) [add_comm_group G]
  : module R (R →+ G) := {
    smul := λ r f, ⟨(λ x, f (x * r)), (by simp), (by { intros, simp [add_mul] })⟩,
    one_smul  := by { intros, simp },
    mul_smul  := by { intros, ext, simp [mul_assoc] },
    smul_add  := by { intros, ext, simp },
    smul_zero := by { intros, ext, simp },
    add_smul  := by { intros, ext, simp [mul_add] },
    zero_smul := by { intros, ext, simp }
  }.

def coextension.map' (R : Type*) [ring R] {G H : Type*} [add_comm_group G] [add_comm_group H]
  (ϕ : G →+ H) : (R →+ G) →ₗ[R] (R →+ H) := {
    to_fun := λ f, ⟨ϕ.comp f, by simp, by { intros, simp }⟩,
    map_add' := by { intros, ext, simp },
    map_smul' := by { intros, ext, simp, refl }
  }.

def Module.coextension (R : Type*) [ring R] : AddCommGroup ⥤ Module R := {
  obj := λ G, Module.of R (R →+ G),
  map := λ G H ϕ, Module.of_hom (coextension.map' R ϕ)
}.

def Module.restriction_coextension_adj_unit (R : Type*) [ring R]
  (M : Type*) [add_comm_group M] [module R M] : M →ₗ[R] (R →+ M) := {
    to_fun := λ x, ⟨(λ r, r • x), zero_smul R x, (λ r s, add_smul r s x)⟩,
    map_add' := by { intros, ext, simp },
    map_smul' := by { intros, ext, simp, symmetry, apply mul_smul }
  }.

def Module.restriction_coextension_adj_counit (R : Type*) [ring R]
  (G : Type*) [add_comm_group G] : (R →+ G) →+ G := {
    to_fun := λ f, f 1,
    map_zero' := rfl,
    map_add' := λ x y, rfl
  }.

def Module.restriction_coextension_adj (R : Type*) [ring R]
  : forget₂ (Module R) AddCommGroup ⊣ Module.coextension R := 
  adjunction.mk_of_unit_counit {
    unit := {
      app := λ M, Module.restriction_coextension_adj_unit R M,
      naturality' := by { intros, ext, symmetry, apply map_smul f }
    },
    counit := {
      app := λ G, Module.restriction_coextension_adj_counit R G,
      naturality' := by { intros, ext, refl }
    },
    left_triangle' := by { ext, exact one_smul _ _ },
    right_triangle' := by { ext M f r, exact congr_arg f.to_fun (one_mul r) } 
  }.

instance Module.forget₂_AddCommGroup_preserves_coproduct {R : Type*} [ring R]
  {J : Type*} (f : J → Module R)
  : limits.preserves_colimit (discrete.functor f) (forget₂ (Module R) AddCommGroup) :=
  @preserves_colimits_of_shape.preserves_colimit _ _ _ _ _ _ _
    (@preserves_colimits_of_size.preserves_colimits_of_shape _ _ _ _ _
      (@preserves_colimits_of_size_shrink _ _ _ _ _
        (Module.restriction_coextension_adj R).left_adjoint_preserves_colimits) _ _) _

lemma sigma_comparison_naturality {β : Type*} {C : Type*} [category C] {D : Type*} [category D]
  (G : C ⥤ D) {f g : β → C} (η : Π (b : β), f b ⟶ g b) [has_coproduct f] [has_coproduct g]
  [has_coproduct (λ (b : β), G.obj (f b))]  [has_coproduct (λ (b : β), G.obj (g b))] 
  : sigma_comparison G f
  ≫ G.map (colim_map (discrete.nat_trans (λ b', η b'.as) : discrete.functor f ⟶ discrete.functor g))
  = colim_map (discrete.nat_trans (λ b', G.map (η b'.as)) : discrete.functor (λ (b : β), G.obj (f b)) ⟶ discrete.functor (λ (b : β), G.obj (g b)))
  ≫ sigma_comparison G g :=
begin
  ext,
  simp [sigma_comparison],
  rw [← G.map_comp, ← G.map_comp],
  refine congr_arg _ _,
  delta sigma.ι,
  simp
end

-- not sure about the universes here
lemma AB4_of_preserves_coproduct_and_reflects_and_preserves_mono {V W : Type u}
  [category.{v} V] [category.{v} W] [abelian V] [abelian W]
  [i : has_coproducts V] [i' : has_coproducts W]
  (F : V ⥤ W) [F.reflects_monomorphisms] [F.preserves_monomorphisms]
  [∀ (J : Type v) (f : J → V), limits.preserves_colimit (discrete.functor f) F]
  [h : @AB4 W _ i'] : @AB4 V _ i := 
begin
  constructor,
  introsI,
  apply F.mono_of_mono_map,
  suffices : mono (F.map (colim_map (discrete.nat_trans (λ a', f a'.as) : discrete.functor X ⟶ discrete.functor Y))),
  { convert this,
    delta sigma.desc cofan.mk colim_map is_colimit.map cocones.precompose,
    congr,
    ext a, cases a, refl },
  have H := sigma_comparison_naturality F f,
  rw ← is_iso.eq_inv_comp at H,
  rw H,
  apply_with mono_comp {instances:=ff},
  { apply_instance },
  { apply_with mono_comp {instances:=ff},
    { convert AB4.cond (F.obj ∘ X) (F.obj ∘ Y) (λ a, F.map (f a)) (λ a, F.map_mono (f a)),
      delta sigma.desc cofan.mk colim_map is_colimit.map cocones.precompose, dsimp,
      congr,
      ext a, cases a, refl },
    { apply_instance } }
end

instance AB4 {R : Type u} [ring R] : AB4 (Module.{(max v u) u} R) :=
  @AB4_of_preserves_coproduct_and_reflects_and_preserves_mono _ _ _ _ _ _ _ _
    (forget₂ (Module.{(max v u) u} R) AddCommGroup.{max v u})
    _ _ 
    (λ J f, @preserves_colimits_of_shape.preserves_colimit _ _ _ _ _ _ _
              (@preserves_colimits_of_size.preserves_colimits_of_shape _ _ _ _ _ 
                (Module.restriction_coextension_adj.{u v} R).left_adjoint_preserves_colimits
                (discrete J) _) (discrete.functor f)) _.