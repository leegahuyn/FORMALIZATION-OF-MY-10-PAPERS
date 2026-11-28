import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineCechAcyclic
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleAffineLowHTwoFromCech

/-! On an affine base whose lifted small étale injectives have exact
positive native Čech cochains, the actual comparison is onto in every
cohomological degree. -/

namespace ManuscriptAudit.EtaleProetaleAffineComparisonAllDegrees

open AlgebraicGeometry CategoryTheory Opposite
open EtaleCoefficientUniverseLift (lift)
open EtaleProetaleInverseImage (adjunction)
open EtaleProetaleAffineLowHTwoFromCech (comparison comparison_succ_surjective liftedImage)
open ProetaleAffineCechHTwo (AffineExactAt)
open ProetaleAffineCechAcyclic (H_succ_subsingleton)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) [IsAffine X]

private abbrev C := Sheaf X.smallEtaleTopology AddCommGrpCat.{0}

set_option maxHeartbeats 5000000 in
/-- The original exact comparison is surjective in all degrees. -/
theorem comparison_surjective
    (hZero : ∀ F : C X, Function.Surjective (((adjunction X).unit.app ((lift X).obj F)).hom.app
      (op (Scheme.Etale.mk (𝟙 X)))))
    (hČech : ∀ I : C X, Injective I → ∀ n, AffineExactAt X ((liftedImage X).obj I) (n + 1))
    (n : ℕ) (F : C X) : Function.Surjective (comparison X F n) := by
  induction n generalizing F with
  | zero =>
      exact (EtaleProetaleHZeroUnitSurjectivity.pullback_zero_surjective X ((lift X).obj F)
        (hZero F)).comp (EtaleCoefficientCohomologyMap.comparison_zero_surjective X F)
  | succ n ih =>
      exact comparison_succ_surjective X n ih
        (fun I hI ↦ H_succ_subsingleton ((liftedImage X).obj I) (hČech I hI) n) F

end
end ManuscriptAudit.EtaleProetaleAffineComparisonAllDegrees

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleProetaleAffineComparisonAllDegrees.comparison_surjective
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
