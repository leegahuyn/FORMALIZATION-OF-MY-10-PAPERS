import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleAffineLowHTwoFromCech

/-! The actual affine-line finite-residue vanishing follows from
the actual affine Čech comparison for small étale injectives. -/

namespace ManuscriptAudit.AffineNativeResidueHTwoFromCech

open AlgebraicGeometry CategoryTheory Opposite
open EtaleCoefficientUniverseLift (lift)
open EtaleProetaleInverseImage (inverseImage adjunction constantInverseImageIso)
open EtaleProetaleAffineLowHTwoFromCech (liftedImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (R₀ : Type) [CommRing R₀]

private abbrev X := Spec (CommRingCat.of R₀)
private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev C := Sheaf (X R₀).smallEtaleTopology A

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (ℓ r : ℕ) [Fact ℓ.Prime]

set_option maxHeartbeats 5400000 in
/-- Actual high-universe native residues on an affine scheme have
zero degree-two cohomology when the actual affine descent inputs hold. -/
theorem native_residue_HTwo_subsingleton
    (hEtale : Subsingleton (Sheaf.H
      ((constantSheaf (X R₀).smallEtaleTopology A).obj (AddCommGrpCat.of (ZMod (ℓ ^ r)))) 2))
    (hZero : ∀ F : C R₀, Function.Surjective
      (((adjunction (X R₀)).unit.app ((lift (X R₀)).obj F)).hom.app
        (op (Scheme.Etale.mk (𝟙 (X R₀))))))
    (hOne : ∀ I : C R₀, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt (X R₀) ((liftedImage (X R₀)).obj I) 1)
    (hTwo : ∀ I : C R₀, Injective I →
      ProetaleAffineCechHTwo.AffineExactAt (X R₀) ((liftedImage (X R₀)).obj I) 2) :
    Subsingleton (Sheaf.H ((ProetaleCoefficientUniverseLift.lift (X R₀)).obj
      (ProetaleResidueSheaves.residueSheaf (X R₀) ℓ r)) 2) := by
  let M := AddCommGrpCat.of (ZMod (ℓ^r))
  let F := (constantSheaf (X R₀).smallEtaleTopology A).obj M
  letI : Subsingleton (Sheaf.H F 2) := hEtale
  have hSource : Subsingleton (Sheaf.H ((liftedImage (X R₀)).obj F) 2) :=
    (EtaleProetaleAffineLowHTwoFromCech.comparison_HTwo_surjective (X R₀) hZero hOne hTwo F).subsingleton
  let M' := (AddCommGrpCat.uliftFunctor.{1} : A ⥤ B).obj M
  let i := (inverseImage (X R₀)).mapIso ((EtaleCoefficientUniverseLift.constantIso (X R₀)).app M) ≪≫
    (constantInverseImageIso (X R₀)).app M' ≪≫
    ProetaleDiscreteConstant.nativeResidueIso (X R₀) ℓ r
  have hI : Function.Injective (Sheaf.H.map i.inv 2) := by
    apply Function.LeftInverse.injective (g := Sheaf.H.map i.hom 2)
    intro x
    rw [← Sheaf.H.map_comp_apply, i.inv_hom_id, Sheaf.H.map_id_apply]
  exact ⟨fun a b ↦ hI (hSource.elim (Sheaf.H.map i.inv 2 a) (Sheaf.H.map i.inv 2 b))⟩

end
end ManuscriptAudit.AffineNativeResidueHTwoFromCech

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.AffineNativeResidueHTwoFromCech.native_residue_HTwo_subsingleton
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
