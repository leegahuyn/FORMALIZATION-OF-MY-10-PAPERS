import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorSheaf
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleClosedFiberSkyscraper
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorByBasePoint

/-!
# Actual divisor-sheaf sections on integral affine étale charts

Each rational skyscraper component carries an integer at each point in
its geometric fiber. The verified finite-support reindexing collects
these coordinates into exactly the finite height-one cycles of the chart.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open IsDedekindDomain GenericEtaleUnitSections AffineEtaleClosedPoints
open AffineLineRationalClosedPoints

noncomputable section

set_option backward.isDefEq.respectTransparency false

private def productAddEquiv {I : Type} (M : AddCommGrpCat.{0}) :
    (∏ᶜ (fun _ : I ↦ M)) ≃+ (I → M) where
  __ := productEquiv (fun _ : I ↦ M)
  map_add' x y := by
    funext i
    simp only [productEquiv_apply_apply, Pi.add_apply]
    exact (Pi.π (fun _ : I ↦ M) i).hom.map_add x y

variable (K B : Type) [Field K] [IsAlgClosed K] [CommRing B] [IsDomain B]
  [Algebra (Polynomial K) B] [Algebra.Etale (Polynomial K) B]

/-- The specified algebra chart as an object of the small affine étale site. -/
def chartObject : (X K).AffineEtale := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) B))
  letI : Etale f := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr (inferInstance : Algebra.Etale (Polynomial K) B))
  exact Scheme.AffineEtale.mk f

private def chartComponentEquiv (p : HeightOneSpectrum (Polynomial K)) :
    (skyscraper K ((closedPointEquiv K).symm p)).obj.obj
        (op (algebraEtaleObject (Polynomial K) B)) ≃+
      ({q : HeightOneSpectrum B // comap (Polynomial K) B q = p} → ℤ) := by
  let a := (closedPointEquiv K).symm p
  letI : Algebra (Polynomial K) K := (Polynomial.evalRingHom a).toAlgebra
  have hp : closedPoint K a = p := (closedPointEquiv K).apply_symm_apply p
  have hs : (Spec.map (CommRingCat.ofHom (algebraMap (Polynomial K) K))
      (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal (rationalPoint_default K a)).trans
      (congrArg HeightOneSpectrum.asIdeal hp)
  have hK : Function.Surjective (algebraMap (Polynomial K) K) := by
    intro c
    exact ⟨Polynomial.C c, Polynomial.eval_C⟩
  let e := rationalSkyscraperHeightOneIso (Polynomial K) B K p hs hK (AddCommGrpCat.of ℤ)
  exact e.addCommGroupIsoToAddEquiv.trans (productAddEquiv (AddCommGrpCat.of ℤ))

set_option maxHeartbeats 1000000 in
/-- The actual finite-support divisor sheaf has the finite height-one
cycles as sections on each integral affine étale chart. -/
def chartSectionsEquiv :
    (affineDivisorSheaf K).obj.obj (op (chartObject K B)) ≃+
      (HeightOneSpectrum B →₀ ℤ) := by
  change (Π₀ p : HeightOneSpectrum (Polynomial K),
    (skyscraper K ((closedPointEquiv K).symm p)).obj.obj
      (op (algebraEtaleObject (Polynomial K) B))) ≃+ _
  exact (DFinsupp.mapRange.addEquiv (chartComponentEquiv K B)).trans
    (cyclesByBasePoint (Polynomial K) B).symm

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.chartSectionsEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
