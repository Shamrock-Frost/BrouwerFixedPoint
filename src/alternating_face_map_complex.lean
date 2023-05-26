import algebraic_topology.alternating_face_map_complex
import category_theory.limits.functor_category
import LTE_port.homological_complex_abelian
import .category_theory

namespace algebraic_topology
namespace alternating_face_map_complex

open category_theory category_theory.limits category_theory.subobject
open category_theory.preadditive category_theory.category
open opposite

universes v' u' v u

noncomputable
instance preserves_limits_of_shape {C : Type u} [category.{v} C] [preadditive C]
  {J : Type u'} [category.{v'} J] [has_limits_of_shape J C]
  : preserves_limits_of_shape J (alternating_face_map_complex C) :=
begin
  constructor, intro K, 
  constructor, intros c hc,
  apply homological_complex.is_limit_of_is_limit_eval,
  intro n,
  let α := functor.associator K (alternating_face_map_complex C) (homological_complex.eval C _ n),
  refine is_limit.equiv_of_nat_iso_of_iso α.symm _ _ (functor.map_cone_map_cone' _ _ _ c) _,
  apply preserves_limits_of_shape.preserves_limit.preserves, exact hc,
  apply limits.evaluation_preserves_limits_of_shape
end

noncomputable instance preserves_limits
  {C : Type u} [category.{v} C] [preadditive C] [has_limits C]
  : preserves_limits (alternating_face_map_complex C) := ⟨⟩.

noncomputable
instance preserves_colimits_of_shape {C : Type u} [category.{v} C] [preadditive C]
  {J : Type u'} [category.{v'} J] [has_colimits_of_shape J C]
  : preserves_colimits_of_shape J (alternating_face_map_complex C) :=
begin
  constructor, intro K, 
  constructor, intros c hc,
  apply homological_complex.is_colimit_of_is_colimit_eval,
  intro n,
  let α := functor.associator K (alternating_face_map_complex C) (homological_complex.eval C _ n),
  refine is_colimit.equiv_of_nat_iso_of_iso α.symm _ _ (functor.map_cocone_map_cocone' _ _ _ c) _,
  apply preserves_colimits_of_shape.preserves_colimit.preserves, exact hc,
  apply limits.evaluation_preserves_colimits_of_shape
end

noncomputable instance preserves_colimits
  {C : Type u} [category.{v} C] [preadditive C] [has_colimits C]
  : preserves_colimits (alternating_face_map_complex C) := ⟨⟩.

end alternating_face_map_complex
end algebraic_topology