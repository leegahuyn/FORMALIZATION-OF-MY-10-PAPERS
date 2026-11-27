import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence

/-!
# Short exactness of quotient invariants when the first H¹ vanishes

The invariants of a short exact sequence of group representations have
the usual left exactness. The actual degree-zero connecting morphism
proves surjectivity when the first term has vanishing subgroup H¹.
-/

namespace ManuscriptAudit.GroupQuotientInvariantSequence

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

variable {k G : Type u} [CommRing k] [Group G]

set_option backward.isDefEq.respectTransparency false in
private theorem invariants_map_epi {W : ShortComplex (Rep.{u} k G)} (hW : W.ShortExact)
    (h : IsZero (groupCohomology W.X₁ 1)) : Epi ((Rep.invariantsFunctor k G).map W.g) := by
  letI : Epi ((groupCohomology.functor k G 0).map W.g) :=
    (groupCohomology.mapShortComplex₃_exact hW (i := 0) (j := 1) rfl).epi_f
      (h.eq_zero_of_tgt _)
  letI : Epi ((groupCohomology.H0Iso W.X₂).hom ≫ (Rep.invariantsFunctor k G).map W.g) := by
    rw [← groupCohomology.map_id_comp_H0Iso_hom]
    change Epi ((groupCohomology.functor k G 0).map W.g ≫ (groupCohomology.H0Iso W.X₃).hom)
    infer_instance
  exact epi_of_epi (groupCohomology.H0Iso W.X₂).hom _

variable (S : Subgroup G) [S.Normal]

set_option backward.isDefEq.respectTransparency false in
private instance quotientInvariantsPreservesZero :
    (Rep.quotientToInvariantsFunctor k S : Rep.{u} k G ⥤ Rep.{u} k (G ⧸ S)).PreservesZeroMorphisms where
  map_zero X Y := by
    ext x
    apply Subtype.ext
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual sequence obtained by applying the quotient invariants
functor is short exact if subgroup H¹ of the first term vanishes. -/
theorem shortExact_quotientToInvariants {X : ShortComplex (Rep.{u} k G)}
    (hX : X.ShortExact) (h : IsZero (groupCohomology (Rep.res S.subtype X.X₁) 1)) :
    (X.map (Rep.quotientToInvariantsFunctor k S)).ShortExact := by
  let W := X.map (Rep.resFunctor S.subtype)
  have hW : W.ShortExact := (Rep.shortExact_res S.subtype).mpr hX
  have hI : Function.Injective W.f.hom := (Rep.mono_iff_injective W.f).mp hW.mono_f
  have hE : Function.Surjective ((Rep.invariantsFunctor k S).map W.g) :=
    (ModuleCat.epi_iff_surjective _).mp (invariants_map_epi hW h)
  let Q := X.map (Rep.quotientToInvariantsFunctor k S)
  refine ShortComplex.ShortExact.mk' (S := Q) ?_ ?_ ?_
  · let C := Q.map (forget₂ (Rep.{u} k (G ⧸ S)) (ModuleCat.{u} k))
    apply (Q.exact_map_iff_of_faithful (forget₂ (Rep.{u} k (G ⧸ S)) (ModuleCat.{u} k))).mp
    show C.Exact
    apply (ShortComplex.moduleCat_exact_iff C).mpr
    intro y hy
    change W.X₂.ρ.invariants at y
    change ((Rep.invariantsFunctor k S).map W.g) y = 0 at hy
    have hy' : W.g.hom y.1 = 0 := congrArg Subtype.val hy
    let D := W.map (forget₂ (Rep.{u} k S) (ModuleCat.{u} k))
    have hD : D.Exact := hW.exact.map (forget₂ (Rep.{u} k S) (ModuleCat.{u} k))
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff D).mp hD y.1 hy'
    change W.f.hom x = y.1 at hx
    have hxFixed : x ∈ W.X₁.ρ.invariants := by
      intro s
      apply hI
      rw [Rep.hom_comm_apply, hx, y.property s]
    exact ⟨(⟨x, hxFixed⟩ : W.X₁.ρ.invariants), Subtype.ext hx⟩
  · apply (Rep.mono_iff_injective Q.f).mpr
    intro x y hxy
    apply Subtype.ext
    apply hI
    exact congrArg Subtype.val hxy
  · exact (Rep.epi_iff_surjective Q.g).mpr hE

end

end ManuscriptAudit.GroupQuotientInvariantSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.GroupQuotientInvariantSequence.shortExact_quotientToInvariants
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
