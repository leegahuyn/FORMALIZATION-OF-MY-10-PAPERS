import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleObjectRestriction
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHZero
import PrimalitySheafVerification.ManuscriptAudit.SheafShortExactSections

/-!
# Exact sections on étale field charts

Restriction of the actual abelian sheaf sequence to the small étale
site of a field is exact. If its first term has zero H¹ there, global
sections over that field chart give a surjection onto the last term.
-/

namespace ManuscriptAudit.EtaleObjectRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

set_option maxHeartbeats 2600000 in
/-- Evaluation of a short exact sequence on an étale field chart is
surjective if the first term has vanishing H¹ on that field site. -/
theorem sections_surjective_of_HOne_of_field
    {X : Scheme.{0}} (S : ShortComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{0}))
    (hS : S.ShortExact) (W : X.Etale) (L : Type) [Field L]
    (e : W.left ≅ Spec (CommRingCat.of L))
    (hVanishing : ∀ (j : Spec (CommRingCat.of L) ⟶ X) [Etale j],
      Subsingleton (Sheaf.H ((restriction j).obj S.X₁) 1)) :
    Function.Surjective (S.g.hom.app (op W)) := by
  let U := Spec (CommRingCat.of L)
  let j : U ⟶ X := e.inv ≫ W.hom
  letI : Etale W.hom := W.prop
  letI : Etale j := by change Etale (e.inv ≫ W.hom); infer_instance
  let R := restriction j
  letI : R.IsLeftAdjoint := (restrictionAdjunction j).isLeftAdjoint
  letI : PreservesFiniteLimits R := restriction_preservesFiniteLimits j
  letI : R.Additive := R.additive_of_preserves_binary_products
  let T : U.Etale := Scheme.Etale.mk (𝟙 U)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal @Etale U
  let S' := S.map R
  have hS' : S'.ShortExact := hS.map_of_exact R
  let V := (postcompose j).obj T
  let e' : V ≅ W := MorphismProperty.Over.isoMk e.symm (by
    change e.inv ≫ W.hom = 𝟙 U ≫ j
    exact (Category.id_comp j).symm)
  have hSurj : Function.Surjective (S.g.hom.app (op V)) :=
    SheafShortExactSections.sections_surjective_of_HOne S' hS' hT (hVanishing j)
  intro y
  obtain ⟨x, hx⟩ := hSurj (S.X₃.obj.map e'.hom.op y)
  refine ⟨S.X₂.obj.map e'.inv.op x, ?_⟩
  calc
    _ = S.X₃.obj.map e'.inv.op (S.g.hom.app (op V) x) :=
      ConcreteCategory.congr_hom (S.g.hom.naturality e'.inv.op) x
    _ = _ := by
      rw [hx]
      exact ((S.X₃.obj.mapIso e'.op).addCommGroupIsoToAddEquiv).symm_apply_apply y

/-- Restriction along the identity of a scheme is naturally the same
sheaf, via the native postcomposition-on-objects isomorphism. -/
def restrictionIdentityIso {X : Scheme.{0}}
    (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{0}) :
    (restriction (𝟙 X)).obj A ≅ A := by
  let e : postcompose (𝟙 X) ≅ 𝟭 X.Etale :=
    MorphismProperty.Over.mapId (P := @Etale) ⊤ X (𝟙 X) rfl
  apply (fullyFaithfulSheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{0}).preimageIso
  change (postcompose (𝟙 X)).op ⋙ A.obj ≅ A.obj
  exact isoWhiskerRight (e.op.symm ≪≫ Functor.opId X.Etale) A.obj ≪≫
    Functor.leftUnitor A.obj

end

end ManuscriptAudit.EtaleObjectRestriction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleObjectRestriction.sections_surjective_of_HOne_of_field,
      ``ManuscriptAudit.EtaleObjectRestriction.restrictionIdentityIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
