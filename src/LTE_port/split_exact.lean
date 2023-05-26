/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang
-/
import category_theory.abelian.diagram_lemmas.four

/-!
# Short exact sequences, and splittings.

`short_exact f g` is the proposition that `0 ⟶ A -f⟶ B -g⟶ C ⟶ 0` is an exact sequence.

We define when a short exact sequence is left-split, right-split, and split.

In an abelian category, a left-split short exact sequence admits a splitting.
-/

noncomputable theory

open category_theory category_theory.limits category_theory.preadditive

variables {𝒜 : Type*} [category 𝒜]

namespace category_theory

variables {A B C A' B' C' : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (f' : A' ⟶ B') (g' : B' ⟶ C')

section has_zero_morphisms

variables [has_zero_morphisms 𝒜] [has_kernels 𝒜] [has_images 𝒜]

/-- If `f : A ⟶ B` and `g : B ⟶ C` then `short_exact f g` is the proposition saying
  the resulting diagram `0 ⟶ A ⟶ B ⟶ C ⟶ 0` is an exact sequence. -/
structure short_exact : Prop :=
[mono  : mono f]
[epi   : epi g]
(exact : exact f g)

open_locale zero_object

-- TODO move
instance zero_to_zero_is_iso {C : Type*} [category C] [has_zero_object C] (f : (0 : C) ⟶ 0) :
  is_iso f :=
by convert (show is_iso (𝟙 (0 : C)), by apply_instance)


/-- An exact sequence `A -f⟶ B -g⟶ C` is *left split*
if there exists a morphism `φ : B ⟶ A` such that `f ≫ φ = 𝟙 A` and `g` is epi.

Such a sequence is automatically short exact (i.e., `f` is mono). -/
structure left_split : Prop :=
(left_split : ∃ φ : B ⟶ A, f ≫ φ = 𝟙 A)
[epi   : epi g]
(exact : exact f g)

lemma left_split.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : left_split f g) : short_exact f g :=
{ mono :=
  begin
    obtain ⟨φ, hφ⟩ := h.left_split,
    haveI : mono (f ≫ φ) := by { rw hφ, apply_instance },
    exact mono_of_mono f φ,
  end,
  epi := h.epi,
  exact := h.exact }

/-- An exact sequence `A -f⟶ B -g⟶ C` is *right split*
if there exists a morphism `φ : C ⟶ B` such that `f ≫ φ = 𝟙 A` and `f` is mono.

Such a sequence is automatically short exact (i.e., `g` is epi). -/
structure right_split : Prop :=
(right_split : ∃ χ : C ⟶ B, χ ≫ g = 𝟙 C)
[mono  : mono f]
(exact : exact f g)

lemma right_split.short_exact {f : A ⟶ B} {g : B ⟶ C} (h : right_split f g) : short_exact f g :=
{ epi :=
  begin
    obtain ⟨χ, hχ⟩ := h.right_split,
    haveI : epi (χ ≫ g) := by { rw hχ, apply_instance },
    exact epi_of_epi χ g,
  end,
  mono := h.mono,
  exact := h.exact }

end has_zero_morphisms

section preadditive

variables [preadditive 𝒜]

/-- An exact sequence `A -f⟶ B -g⟶ C` is *split* if there exist
`φ : B ⟶ A` and `χ : C ⟶ B` such that:
* `f ≫ φ = 𝟙 A`
* `χ ≫ g = 𝟙 C`
* `f ≫ g = 0`
* `χ ≫ φ = 0`
* `φ ≫ f + g ≫ χ = 𝟙 B`

Such a sequence is automatically short exact (i.e., `f` is mono and `g` is epi). -/
structure split : Prop :=
(split : ∃ (φ : B ⟶ A) (χ : C ⟶ B),
  f ≫ φ = 𝟙 A ∧ χ ≫ g = 𝟙 C ∧ f ≫ g = 0 ∧ χ ≫ φ = 0 ∧ φ ≫ f + g ≫ χ = 𝟙 B)

variables [has_kernels 𝒜] [has_images 𝒜]

lemma exact_of_split {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (χ : C ⟶ B) (φ : B ⟶ A)
  (hfg : f ≫ g = 0) (H : φ ≫ f + g ≫ χ = 𝟙 B) : exact f g :=
{ w := hfg,
  epi :=
  begin
    let ψ : (kernel_subobject g : 𝒜) ⟶ image_subobject f :=
      subobject.arrow _ ≫ φ ≫ factor_thru_image_subobject f,
    suffices : ψ ≫ image_to_kernel f g hfg = 𝟙 _,
    { convert epi_of_epi ψ _, rw this, apply_instance },
    rw ← cancel_mono (subobject.arrow _), swap, { apply_instance },
    simp only [image_to_kernel_arrow, image_subobject_arrow_comp, category.id_comp, category.assoc],
    calc (kernel_subobject g).arrow ≫ φ ≫ f
        = (kernel_subobject g).arrow ≫ 𝟙 B : _
    ... = (kernel_subobject g).arrow        : category.comp_id _,
    rw [← H, preadditive.comp_add],
    simp only [add_zero, zero_comp, kernel_subobject_arrow_comp_assoc],
  end }

section

variables {f g}

lemma split.exact (h : split f g) : exact f g :=
by { obtain ⟨φ, χ, -, -, h1, -, h2⟩ := h, exact exact_of_split f g χ φ h1 h2 }

lemma split.left_split (h : split f g) : left_split f g :=
{ left_split := by { obtain ⟨φ, χ, h1, -⟩ := h, exact ⟨φ, h1⟩, },
  epi := begin
    obtain ⟨φ, χ, -, h2, -⟩ := h,
    have : epi (χ ≫ g), { rw h2, apply_instance },
    exactI epi_of_epi χ g,
  end,
  exact := h.exact }

lemma split.right_split (h : split f g) : right_split f g :=
{ right_split := by { obtain ⟨φ, χ, -, h1, -⟩ := h, exact ⟨χ, h1⟩, },
  mono := begin
    obtain ⟨φ, χ, h1, -⟩ := h,
    have : mono (f ≫ φ), { rw h1, apply_instance },
    exactI mono_of_mono f φ,
  end,
  exact := h.exact }

lemma split.short_exact (h : split f g) : short_exact f g :=
h.left_split.short_exact

end

lemma split.map {𝒜 ℬ : Type*} [category 𝒜] [abelian 𝒜] [category ℬ] [abelian ℬ] (F : 𝒜 ⥤ ℬ)
  [functor.additive F] {A B C : 𝒜} (f : A ⟶ B) (g : B ⟶ C) (h : split f g) :
  split (F.map f) (F.map g) :=
begin
  obtain ⟨φ, χ, h1, h2, h3, h4, h5⟩ := h,
  refine ⟨⟨F.map φ, F.map χ, _⟩⟩,
  simp only [← F.map_comp, ← F.map_id, ← F.map_add, F.map_zero, *, eq_self_iff_true, and_true],
end

/-- The sequence `A ⟶ A ⊞ B ⟶ B` is exact. -/
lemma exact_inl_snd [has_binary_biproducts 𝒜] (A B : 𝒜) :
  exact (biprod.inl : A ⟶ A ⊞ B) biprod.snd :=
exact_of_split _ _ biprod.inr biprod.fst biprod.inl_snd biprod.total

/-- The sequence `B ⟶ A ⊞ B ⟶ A` is exact. -/
lemma exact_inr_fst [has_binary_biproducts 𝒜] (A B : 𝒜) :
  exact (biprod.inr : B ⟶ A ⊞ B) biprod.fst :=
exact_of_split _ _ biprod.inl biprod.snd biprod.inr_fst ((add_comm _ _).trans biprod.total)

end preadditive

section abelian

variables [abelian 𝒜]
open_locale zero_object

lemma is_iso_of_short_exact_of_is_iso_of_is_iso (h : short_exact f g) (h' : short_exact f' g')
  (i₁ : A ⟶ A') (i₂ : B ⟶ B') (i₃ : C ⟶ C')
  (comm₁ : i₁ ≫ f' = f ≫ i₂) (comm₂ : i₂ ≫ g' = g ≫ i₃) [is_iso i₁] [is_iso i₃] :
  is_iso i₂ :=
begin
  destruct h, intros,
  destruct h', intros,
  resetI,
  refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso 𝒜 _ _ 0 _ _ _ 0 _ _ _
    0 f g 0 f' g' 0 i₁ i₂ i₃ _ comm₁ comm₂ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _;
  try { simp };
  try { apply exact_zero_left_of_mono };
  try { assumption };
  rwa ← epi_iff_exact_zero_right,
end

end abelian

/-- A *splitting* of a sequence `A -f⟶ B -g⟶ C` is an isomorphism
to the short exact sequence `0 ⟶ A ⟶ A ⊞ C ⟶ C ⟶ 0` such that
the vertical maps on the left and the right are the identity. -/
@[nolint has_inhabited_instance]
structure splitting [has_zero_morphisms 𝒜] [has_binary_biproducts 𝒜] :=
(iso : B ≅ A ⊞ C)
(comp_iso_eq_inl : f ≫ iso.hom = biprod.inl)
(iso_comp_snd_eq : iso.hom ≫ biprod.snd = g)

variables {f g}

namespace splitting

section has_zero_morphisms
variables [has_zero_morphisms 𝒜] [has_binary_biproducts 𝒜]

attribute [simp, reassoc] comp_iso_eq_inl iso_comp_snd_eq

variables (h : splitting f g)

@[simp, reassoc] lemma inl_comp_iso_eq : biprod.inl ≫ h.iso.inv = f :=
by rw [iso.comp_inv_eq, h.comp_iso_eq_inl]

@[simp, reassoc] lemma iso_comp_eq_snd : h.iso.inv ≫ g = biprod.snd :=
by rw [iso.inv_comp_eq, h.iso_comp_snd_eq]

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.section : C ⟶ B` is the morphism satisfying `h.section ≫ g = 𝟙 C`. -/
def _root_.category_theory.splitting.section : C ⟶ B := biprod.inr ≫ h.iso.inv

/-- If `h` is a splitting of `A -f⟶ B -g⟶ C`,
then `h.retraction : B ⟶ A` is the morphism satisfying `f ≫ h.retraction = 𝟙 A`. -/
def retraction : B ⟶ A := h.iso.hom ≫ biprod.fst

@[simp, reassoc] lemma section_π : h.section ≫ g = 𝟙 C := by { delta splitting.section, simp }

@[simp, reassoc] lemma ι_retraction : f ≫ h.retraction = 𝟙 A := by { delta retraction, simp }

@[simp, reassoc] lemma section_retraction : h.section ≫ h.retraction = 0 :=
by { delta splitting.section retraction, simp }

/-- The retraction in a splitting is a split mono. -/
protected def split_mono : split_mono f := ⟨h.retraction, by simp⟩

/-- The section in a splitting is a split epi. -/
protected def split_epi : split_epi g := ⟨h.section, by simp⟩

@[simp, reassoc] lemma inr_iso_inv : biprod.inr ≫ h.iso.inv = h.section := rfl

@[simp, reassoc] lemma iso_hom_fst : h.iso.hom ≫ biprod.fst = h.retraction := rfl

-- move this, add `iso_zero_biprod`
/-- If `Y` is a zero object, `X ≅ X ⊞ Y` for any `X`. -/
@[simps]
def iso_biprod_zero {C : Type*} [category C] [has_zero_morphisms C]
  [has_binary_biproducts C] {X Y : C} (hY : is_zero Y) : X ≅ X ⊞ Y :=
{ hom := biprod.inl,
  inv := biprod.fst,
  inv_hom_id' := begin
    apply category_theory.limits.biprod.hom_ext;
    simp only [category.assoc, biprod.inl_fst, category.comp_id, category.id_comp,
      biprod.inl_snd, comp_zero],
    apply hY.eq_of_tgt
  end }
.

/-- A short exact sequence of the form `X -f⟶ Y -0⟶ Z` where `f` is an iso and `Z` is zero
has a splitting. -/
def splitting_of_is_iso_zero {X Y Z : 𝒜} (f : X ⟶ Y) [is_iso f] (hZ : is_zero Z) :
  splitting f (0 : Y ⟶ Z) :=
⟨(as_iso f).symm ≪≫ iso_biprod_zero hZ, by simp [hZ.eq_of_tgt _ 0], by simp⟩

include h

protected lemma mono : mono f :=
begin
  apply mono_of_mono _ h.retraction,
  rw h.ι_retraction,
  apply_instance
end

protected lemma epi : epi g :=
begin
  apply_with (epi_of_epi h.section) { instances := ff },
  rw h.section_π,
  apply_instance
end

instance : mono h.section :=
by { delta splitting.section, apply_instance }

instance : epi h.retraction :=
by { delta retraction, apply epi_comp }

end has_zero_morphisms

section preadditive
variables [preadditive 𝒜] [has_binary_biproducts 𝒜]
variables (h : splitting f g)

lemma split_add : h.retraction ≫ f + g ≫ h.section = 𝟙 _ :=
begin
  delta splitting.section retraction,
  rw [← cancel_mono h.iso.hom, ← cancel_epi h.iso.inv],
  simp only [category.comp_id, category.id_comp, category.assoc,
    iso.inv_hom_id_assoc, iso.inv_hom_id, limits.biprod.total,
    preadditive.comp_add, preadditive.add_comp,
    splitting.comp_iso_eq_inl, splitting.iso_comp_eq_snd_assoc]
end

@[reassoc]
lemma retraction_ι_eq_id_sub :
  h.retraction ≫ f = 𝟙 _ - g ≫ h.section :=
eq_sub_iff_add_eq.mpr h.split_add

@[reassoc]
lemma π_section_eq_id_sub :
  g ≫ h.section = 𝟙 _ - h.retraction ≫ f :=
eq_sub_iff_add_eq.mpr ((add_comm _ _).trans h.split_add)

lemma splittings_comm (h h' : splitting f g) :
  h'.section ≫ h.retraction = - h.section ≫ h'.retraction :=
begin
  haveI := h.mono,
  rw ← cancel_mono f,
  simp [retraction_ι_eq_id_sub],
end

include h

lemma split : split f g :=
begin
  let φ := h.iso.hom ≫ biprod.fst,
  let χ := biprod.inr ≫ h.iso.inv,
  refine ⟨⟨h.retraction, h.section, h.ι_retraction, h.section_π, _,
    h.section_retraction, h.split_add⟩⟩,
  rw [← h.inl_comp_iso_eq, category.assoc, h.iso_comp_eq_snd, biprod.inl_snd],
end

@[reassoc] lemma comp_eq_zero : f ≫ g = 0 :=
h.split.1.some_spec.some_spec.2.2.1

variables [has_kernels 𝒜] [has_images 𝒜] [has_zero_object 𝒜] [has_cokernels 𝒜]

protected lemma exact : exact f g :=
begin
  rw exact_iff_exact_of_iso f g (biprod.inl : A ⟶ A ⊞ C) (biprod.snd : A ⊞ C ⟶ C) _ _ _,
  { exact exact_inl_snd _ _ },
  { refine arrow.iso_mk (iso.refl _) h.iso _,
    simp only [iso.refl_hom, arrow.mk_hom, category.id_comp, comp_iso_eq_inl], },
  { refine arrow.iso_mk h.iso (iso.refl _) _,
    simp only [iso.refl_hom, arrow.mk_hom, category.comp_id, iso_comp_snd_eq],
    erw category.comp_id /- why ?? -/ },
  { refl }
end

protected
lemma short_exact : short_exact f g :=
{ mono := h.mono, epi := h.epi, exact := h.exact }

end preadditive

section abelian
variables [abelian 𝒜]

-- TODO: this should be generalized to isoms of short sequences,
-- because now it forces one direction, and we want both.
/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is than automatically an isomorphism. -/
def mk' (h : short_exact f g) (i : B ⟶ A ⊞ C) (h1 : f ≫ i = biprod.inl) (h2 : i ≫ biprod.snd = g) :
  splitting f g :=
{ iso :=
  begin
    refine @as_iso _ _ _ _ i (id _),
    refine is_iso_of_short_exact_of_is_iso_of_is_iso f g _ _ h _ _ _ _
      (h1.trans (category.id_comp _).symm).symm (h2.trans (category.comp_id _).symm),
    split,
    apply exact_inl_snd
  end,
  comp_iso_eq_inl := by { rwa as_iso_hom, },
  iso_comp_snd_eq := h2 }

end abelian

end splitting

section
variables [abelian 𝒜]

/-- A short exact sequence that is left split admits a splitting. -/
def left_split.splitting {f : A ⟶ B} {g : B ⟶ C} (h : left_split f g) : splitting f g :=
splitting.mk' h.short_exact (biprod.lift h.left_split.some g)
(by { ext,
  { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec },
  { simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w], } })
(by { simp only [biprod.lift_snd], })

end

end category_theory
