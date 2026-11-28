import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import PrimalitySheafVerification.ManuscriptAudit.FlatSurjectionLocalizationLift

/-! An actual affine flat closed graph lifts to a weakly étale chart. -/

namespace ManuscriptAudit.AffineFlatClosedGraphLift

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FlatSurjectionLocalizationLift

noncomputable section
universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private theorem localization_weaklyEtale {R : Type u} [CommRing R] (M : Submonoid R) :
    WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R (Localization M)))) := by
  let f := CommRingCat.ofHom (algebraMap R (Localization M))
  letI : Epi f := ⟨fun a b h ↦ by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext M
    exact congrArg CommRingCat.Hom.hom h⟩
  have hf : Flat (Spec.map f) := Flat.SpecMap_iff.mpr <|
    RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ M)
  letI : Mono (Spec.map f) := by
    change Mono (Scheme.Spec.map f.op)
    infer_instance
  exact ⟨hf, inferInstance⟩

/-- A flat closed affine graph is the pullback of an affine weakly étale chart. -/
theorem exists_weaklyEtale_pullback {P F W : Scheme.{u}} [IsAffine P]
    (k : F ⟶ P) (g : W ⟶ F) [IsClosedImmersion k] [IsClosedImmersion g] [Flat g] :
    ∃ (V : Scheme.{u}) (_ : IsAffine V) (j : V ⟶ P) (_ : WeaklyEtale j) (t : W ⟶ V),
      IsPullback t g j k := by
  letI : IsAffine F := (IsClosedImmersion.isAffine_surjective_of_isAffine k).1
  letI : IsAffine W := (IsClosedImmersion.isAffine_surjective_of_isAffine g).1
  let R : CommRingCat.{u} := Γ(P, ⊤)
  let D : CommRingCat.{u} := Γ(F, ⊤)
  let E : CommRingCat.{u} := Γ(W, ⊤)
  letI : Algebra R D := k.appTop.hom.toAlgebra
  letI : Algebra D E := g.appTop.hom.toAlgebra
  letI : Module.Flat D E := g.flat_appTop
  let L := Ambient R D E
  let f : R ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap R L)
  let d : CommRingCat.of L ⟶ E := CommRingCat.ofHom (lift R D E)
  have hp : IsPushout k.appTop f g.appTop d :=
    FlatSurjectionLocalizationLift.isPushout R D E
      (IsClosedImmersion.isAffine_surjective_of_isAffine k).2
      (IsClosedImmersion.isAffine_surjective_of_isAffine g).2
  have hq : IsPullback (Spec.map g.appTop) (Spec.map d) (Spec.map k.appTop) (Spec.map f) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ hp
  let V := Spec (CommRingCat.of L)
  let j : V ⟶ P := Spec.map f ≫ P.isoSpec.inv
  let t : W ⟶ V := W.isoSpec.hom ≫ Spec.map d
  letI : WeaklyEtale (Spec.map f) := localization_weaklyEtale (denominators R D E)
  have hj : WeaklyEtale j := by
    change WeaklyEtale (Spec.map f ≫ P.isoSpec.inv)
    infer_instance
  refine ⟨V, inferInstance, j, hj, t, ?_⟩
  refine hq.flip.of_iso' W.isoSpec (Iso.refl _) F.isoSpec P.isoSpec ?_ ?_ ?_ ?_
  · simp [t]
  · exact (Scheme.isoSpec_hom_naturality g).symm
  · simp [j, Category.assoc]
  · exact (Scheme.isoSpec_hom_naturality k).symm

end
end ManuscriptAudit.AffineFlatClosedGraphLift

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineFlatClosedGraphLift.exists_weaklyEtale_pullback
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
