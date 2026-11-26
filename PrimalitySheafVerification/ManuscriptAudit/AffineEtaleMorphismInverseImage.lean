import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismLimits
import PrimalitySheafVerification.ManuscriptAudit.EssentiallySmallSitePullback

/-!
# The exact inverse image of a morphism of affine spectra

The actual full étale direct image is compared to the affine-site
direct image. Its left adjoint, transported from the small model
of the affine site, preserves finite limits. Consequently the
native full direct image preserves injective abelian sheaves.
-/

namespace ManuscriptAudit.AffineEtaleMorphism

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R S : CommRingCat.{u}) (f : Spec S ⟶ Spec R)

private abbrev A := AddCommGrpCat.{u}
private abbrev EX (S : CommRingCat.{u}) := Scheme.AffineEtale.sheafEquiv (Spec S) A.{u}
private abbrev J (S : CommRingCat.{u}) := Scheme.AffineEtale.topology (Spec S)
private abbrev T (S : CommRingCat.{u}) := (Spec S).smallEtaleTopology

set_option maxHeartbeats 2500000 in
/-- The actual full étale direct image for a morphism of affine spectra
has a left adjoint preserving finite limits. -/
theorem fullDirectImage_hasLeftExactLeftAdjoint :
    ∃ L : Sheaf (T R) A.{u} ⥤ Sheaf (T S) A.{u},
      Nonempty (L ⊣ SmallEtaleBaseChange.directImage f A.{u}) ∧ PreservesFiniteLimits L := by
  let g := baseChange f
  let h := SmallEtaleBaseChange.etaleBaseChange f
  let p := Scheme.AffineEtale.Spec (Spec S)
  let q := Scheme.AffineEtale.Spec (Spec R)
  letI : HasFiniteLimits (Spec R).AffineEtale := spec_hasFiniteLimits R
  letI : PreservesFiniteLimits g := baseChange_preservesFiniteLimits R S f
  letI : g.IsContinuous (J R) (J S) := baseChange_isContinuous R S f
  letI : h.IsContinuous (T R) (T S) := SmallEtaleBaseChange.isContinuous_of_baseChange f
  letI := Functor.isContinuous_comp g p (J R) (J S) (T S)
  letI := Functor.isContinuous_comp q h (J R) (T R) (T S)
  obtain ⟨L₀, ⟨a₀⟩, hL⟩ :=
    EssentiallySmallSitePullback.exists_leftExactLeftAdjoint (J R) (J S) g
  letI : PreservesFiniteLimits L₀ := hL
  let D := SmallEtaleBaseChange.directImage f A.{u}
  let P := g.sheafPushforwardContinuous A.{u} (J R) (J S)
  let e₀ : (EX S).inverse ⋙ P ≅ D ⋙ (EX R).inverse :=
    Functor.sheafPushforwardContinuousComp (F := g) (G := p) (A := A.{u})
      (J := J R) (K := J S) (L := T S) ≪≫
    Functor.sheafPushforwardContinuousIso (baseChangeSpecIso f) (A := A.{u})
      (J := J R) (K := T S) ≪≫
    (Functor.sheafPushforwardContinuousComp (F := q) (G := h) (A := A.{u})
      (J := J R) (K := T R) (L := T S)).symm
  let e : (EX S).inverse ⋙ P ⋙ (EX R).functor ≅ D :=
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight e₀ (EX R).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft D (EX R).counitIso ≪≫
    D.rightUnitor
  let L := ((EX R).inverse ⋙ L₀) ⋙ (EX S).functor
  let a := (((EX R).symm.toAdjunction.comp a₀).comp (EX S).toAdjunction).ofNatIsoRight e
  exact ⟨L, ⟨a⟩, inferInstance⟩

/-- The actual full small étale direct image preserves injective sheaves. -/
theorem fullDirectImage_preservesInjectiveObjects :
    (SmallEtaleBaseChange.directImage f A.{u}).PreservesInjectiveObjects := by
  obtain ⟨L, ⟨a⟩, hL⟩ := fullDirectImage_hasLeftExactLeftAdjoint R S f
  letI : PreservesFiniteLimits L := hL
  exact Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms a

end

end ManuscriptAudit.AffineEtaleMorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleMorphism.fullDirectImage_hasLeftExactLeftAdjoint,
      ``ManuscriptAudit.AffineEtaleMorphism.fullDirectImage_preservesInjectiveObjects] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
