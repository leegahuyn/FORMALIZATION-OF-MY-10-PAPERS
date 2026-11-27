import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.RatFunc.Basic
import PrimalitySheafVerification.ManuscriptAudit.AffineLineGenericCohomologyInjection
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportDegreeTwoQuotient
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportHigherComparison

/-!
# Degree-two compact-support groups from the fraction-field unit cohomology

Vanishing of the actual rational function field unit cohomology kills
both chart terms in Mayer–Vietoris. The cyclic overlap then exhausts
the compactly supported cohomology of the cusp and its puncture.
-/

namespace ManuscriptAudit.CuspCompactSupportDegreeTwo

open AlgebraicGeometry CategoryTheory
open CuspCompactSupportSequence KummerCohomologyDegreeTwo KummerUnitsSheaf

noncomputable section

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt
  KummerCohomologySequence.affineSiteHasExt

variable (K : Type) [Field K] [IsAlgClosed K]

/-- The field-side vanishing forces the actual affine-line cyclic group in degree two to vanish. -/
theorem affineLine_cyclic_HTwo_subsingleton_of_field (ℓ : ℕ) [NeZero (ℓ : K)]
    (hField : Subsingleton
      (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))) 2)) :
    Subsingleton (Sheaf.H
      ((constantSheaf (Spec (CommRingCat.of (Polynomial K))).smallEtaleTopology
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod ℓ))) 2) := by
  let e := AffineLineDivisorSheaf.affineLineCyclicHTwoEmbedding K (RatFunc K) ℓ
  exact ⟨fun x y ↦ e.property (hField.elim (e.val x) (e.val y))⟩

variable (p : ℕ) [Fact p.Prime] [CharP K p]
variable (ℓ : ℕ) [NeZero (ℓ : K)]

/-- If the rational function field has vanishing degree-two unit
cohomology, the actual compactly supported degree-two cusp group
is the cyclic overlap group. -/
theorem nonempty_cuspHcTwoEquiv_of_field (hℓ : 2 ≤ ℓ)
    (hField : Subsingleton
      (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))) 2)) :
    Nonempty (cuspHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) := by
  let e := affineLineCyclicHTwoEquiv K ℓ
  have hLine := affineLine_cyclic_HTwo_subsingleton_of_field K ℓ hField
  letI : Subsingleton (affineLineUnitTorsion K ℓ) :=
    ⟨fun x y ↦ e.symm.injective (hLine.elim (e.symm x) (e.symm y))⟩
  obtain ⟨f, g, hInjective, hExact⟩ := cuspHcTwo_exact_with_affineUnitTorsion K p ℓ hℓ
  have hSurjective : Function.Surjective f := fun x ↦ (hExact x).mp (Subsingleton.elim _ _)
  exact ⟨(AddEquiv.ofBijective f ⟨hInjective, hSurjective⟩).symm⟩

/-- The punctured cusp has the same actual compactly supported group in degree two. -/
theorem nonempty_punctureHcTwoEquiv_of_field (hℓ : 2 ≤ ℓ)
    (hField : Subsingleton
      (Sheaf.H (fullCoordinateUnitSheaf (Spec (CommRingCat.of (RatFunc K)))) 2)) :
    Nonempty (punctureHc K (AddCommGrpCat.of (ZMod ℓ)) 2 ≃+ ZMod ℓ) := by
  obtain ⟨e⟩ := nonempty_cuspHcTwoEquiv_of_field K p ℓ hℓ hField
  exact ⟨(compactSupportHigherEquiv K (AddCommGrpCat.of (ZMod ℓ)) 0).trans e⟩

end

end ManuscriptAudit.CuspCompactSupportDegreeTwo

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspCompactSupportDegreeTwo.affineLine_cyclic_HTwo_subsingleton_of_field,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_cuspHcTwoEquiv_of_field,
      ``ManuscriptAudit.CuspCompactSupportDegreeTwo.nonempty_punctureHcTwoEquiv_of_field] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
