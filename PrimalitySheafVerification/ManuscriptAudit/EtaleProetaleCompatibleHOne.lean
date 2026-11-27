import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CompatibleTowerCongruence
import PrimalitySheafVerification.ManuscriptAudit.EtaleProetaleFiniteHOneComparison

/-! The actual site comparison is compatible with reduction of the finite coefficients. -/

namespace ManuscriptAudit.EtaleProetaleCompatibleHOne

open AlgebraicGeometry CategoryTheory
open CyclicPowerInverseLimit (compatibleTuples)
open EtaleProetaleFiniteHOneComparison (comparison comparison_injective etaleCoefficient)
open EtaleProetaleResidueComparison (directImage residueDirectImageIso
  residueDirectImageIso_naturality)
open ProetaleAdicHOneDetection (compatibleHOne finiteCoefficient)
open ProetaleResidueSheaves (residueSheaf residueTransition)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The actual reduction of constant finite coefficients on the small étale site. -/
abbrev etaleReduction (n : ℕ) : etaleCoefficient X ℓ (n + 1) ⟶ etaleCoefficient X ℓ n :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{0}).map
    (AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom)

abbrev etaleTransition (n : ℕ) := Sheaf.H.map (etaleReduction X ℓ n) 1

abbrev nativeTransition (n : ℕ) :=
  Sheaf.H.map ((ProetaleCoefficientUniverseLift.lift X).map (residueTransition X ℓ n)) 1

/-- The compatible tower of ordinary small-étale cohomology of the actual finite constants. -/
abbrev etaleCompatibleHOne :=
  compatibleTuples (fun n ↦ Sheaf.H (etaleCoefficient X ℓ n) 1) (etaleTransition X ℓ)

/-- The finite site comparisons commute with the actual coefficient reductions on both sites. -/
theorem comparison_naturality (n : ℕ) (x : Sheaf.H (etaleCoefficient X ℓ (n + 1)) 1) :
    comparison X ℓ n (etaleTransition X ℓ n x) =
      nativeTransition X ℓ n (comparison X ℓ (n + 1) x) := by
  let f := residueTransition X ℓ n
  change EtaleProetaleHOneUniverseComparison.comparison X (residueSheaf X ℓ n)
    (Sheaf.H.map (residueDirectImageIso X ℓ n).inv 1
      (Sheaf.H.map (etaleReduction X ℓ n) 1 x)) =
    nativeTransition X ℓ n
      (EtaleProetaleHOneUniverseComparison.comparison X (residueSheaf X ℓ (n + 1))
        (Sheaf.H.map (residueDirectImageIso X ℓ (n + 1)).inv 1 x))
  rw [← Sheaf.H.map_comp_apply]
  have h : etaleReduction X ℓ n ≫ (residueDirectImageIso X ℓ n).inv =
      (residueDirectImageIso X ℓ (n + 1)).inv ≫ (directImage X).map f :=
    residueDirectImageIso_naturality X ℓ n
  rw [h, Sheaf.H.map_comp_apply]
  exact EtaleProetaleHOneUniverseComparison.comparison_naturality X f _

set_option maxHeartbeats 1200000 in
/-- When the actual comparisons are surjective at every finite order, they are an
additive equivalence of the compatible degree-one towers. -/
def comparisonEquiv (onto : ∀ n, Function.Surjective (comparison X ℓ n)) :
    etaleCompatibleHOne X ℓ ≃+ compatibleHOne X ℓ := by
  let E (n : ℕ) := Sheaf.H (etaleCoefficient X ℓ n) 1
  let N (n : ℕ) := Sheaf.H (finiteCoefficient X ℓ n) 1
  let e (n : ℕ) : E n ≃+ N n :=
    AddEquiv.ofBijective (comparison X ℓ n) ⟨comparison_injective X ℓ n, onto n⟩
  refine CompatibleTowerCongruence.compatibleEquiv E N (etaleTransition X ℓ)
    (nativeTransition X ℓ) e ?_
  intro n x
  exact comparison_naturality X ℓ n x

set_option maxHeartbeats 1200000 in
/-- At each finite order the compatible equivalence uses the actual site comparison. -/
theorem comparisonEquiv_apply (onto : ∀ n, Function.Surjective (comparison X ℓ n))
    (x : etaleCompatibleHOne X ℓ) (n : ℕ) :
    (comparisonEquiv X ℓ onto x).val n = comparison X ℓ n (x.val n) := rfl

end
end ManuscriptAudit.EtaleProetaleCompatibleHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.EtaleProetaleCompatibleHOne.comparison_naturality,
      ``ManuscriptAudit.EtaleProetaleCompatibleHOne.comparisonEquiv,
      ``ManuscriptAudit.EtaleProetaleCompatibleHOne.comparisonEquiv_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
