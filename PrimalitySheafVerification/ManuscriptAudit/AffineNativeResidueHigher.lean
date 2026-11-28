import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleAffineComparisonAllDegrees
import PrimalitySheafVerification.ManuscriptAudit.AffineNativeResidueHTwoOfApproximation
import PrimalitySheafVerification.ManuscriptAudit.AffineLineEtaleAcyclic
import PrimalitySheafVerification.ManuscriptAudit.PrincipalOpenEtaleAcyclic

/-! The actual finite native residue cohomology inherits small étale
vanishing in all degrees on the affine line and its principal opens. -/

namespace ManuscriptAudit.AffineNativeResidueHigher

open AlgebraicGeometry CategoryTheory Opposite
open EtaleBaseChangeFiniteApproximation (HasWeaklyEtaleApproximations)
open EtaleProetaleAffineLowHTwoFromCech (liftedImage)
open EtaleProetaleInverseImage (inverseImage constantInverseImageIso)
open EtaleCoefficientUniverseLift (lift constantIso)
open ProetaleAdicHOneDetection (finiteCoefficient)
open ProetaleDiscreteConstant (nativeResidueIso)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev X (R : Type) [CommRing R] := Spec (CommRingCat.of R)

private abbrev F (R : Type) [CommRing R] (d : ℕ) :=
  (constantSheaf (X R).smallEtaleTopology A).obj (AddCommGrpCat.of (ZMod d))

set_option maxHeartbeats 6200000 in
/-- For actual cyclic coefficient sheaves, vanishing transfers in any degree. -/
theorem residue_subsingleton (R : Type) [CommRing R] (hApprox : HasWeaklyEtaleApproximations R)
    (l r : ℕ) [Fact l.Prime] (n : ℕ) (hEtale : Subsingleton (Sheaf.H (F R (l ^ r)) n)) :
    Subsingleton (Sheaf.H (finiteCoefficient (X R) l r) n) := by
  let M := AddCommGrpCat.of (ZMod (l ^ r))
  let M' := (AddCommGrpCat.uliftFunctor.{1} : A ⥤ B).obj M
  let j := (inverseImage (X R)).mapIso ((constantIso (X R)).app M) ≪≫
    (constantInverseImageIso (X R)).app M' ≪≫ nativeResidueIso (X R) l r
  let e := cohomologyIso j n
  letI := hEtale
  have h : Subsingleton (Sheaf.H ((liftedImage (X R)).obj (F R (l ^ r))) n) :=
    (EtaleProetaleAffineComparisonAllDegrees.comparison_surjective (X R)
      (fun T ↦ AffineNativeRawSectionsOfApproximation.unit_terminal_surjective R hApprox
        ((lift (X R)).obj T))
      (fun I hi d ↦ by
        letI := hi
        exact AffineNativeResidueHTwoOfApproximation.affine_exactAt_succ R hApprox I d)
      n (F R (l ^ r))).subsingleton
  exact ⟨fun a b ↦ e.symm.injective (h.elim (e.symm a) (e.symm b))⟩

variable (K : Type) [Field K] [IsAlgClosed K] (l r : ℕ)
  [Fact l.Prime] [NeZero ((l ^ r : ℕ) : K)]

/-- The actual affine line is pro-étale acyclic in every positive finite residue degree. -/
theorem affineLine_succ_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X (Polynomial K)) l r) (n + 1)) :=
  residue_subsingleton (Polynomial K) (EtaleBaseChangeFiniteApproximation.affineLine K) l r (n + 1)
    (AffineLineEtaleAcyclic.cyclic_H_succ_subsingleton K (l ^ r) n)

/-- Every actual nonempty principal affine open is pro-étale acyclic from degree two. -/
theorem principalOpen_add_two_subsingleton (g : Polynomial K) (hg : g ≠ 0) (n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X (Localization.Away g)) l r) (n + 2)) :=
  residue_subsingleton (Localization.Away g) (EtaleBaseChangeFiniteApproximation.principalOpen K g)
    l r (n + 2) (PrincipalOpenEtaleAcyclic.cyclic_H_add_two_subsingleton K g hg (l ^ r) n)

end
end ManuscriptAudit.AffineNativeResidueHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineNativeResidueHigher.residue_subsingleton,
      ``ManuscriptAudit.AffineNativeResidueHigher.affineLine_succ_subsingleton,
      ``ManuscriptAudit.AffineNativeResidueHigher.principalOpen_add_two_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
