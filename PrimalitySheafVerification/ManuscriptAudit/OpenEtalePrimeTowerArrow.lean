import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.OpenEtaleSectionTower
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! The classical tower arrows use the same actual native residue reductions as the p-adic sheaf. -/

namespace ManuscriptAudit.OpenEtalePrimeTowerArrow

open AlgebraicGeometry CategoryTheory
open OpenEtaleCoefficientReduction (extendedConstants)
open OpenEtaleSectionTower (coefficientTransition coefficients)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev M (d : ℕ) := AddCommGrpCat.of (ZMod d)

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- The native coefficient arrow is the actual finite p-adic residue reduction. -/
def residueArrow (r : ℕ) : M (ℓ ^ (r + 1)) ⟶ M (ℓ ^ r) :=
  AddCommGrpCat.ofHom (PadicResidueSystems.reduction ℓ (Nat.le_succ r)).toAddMonoidHom

private def groupOrderHom {a b : ℕ} (h : a = b) : M a ⟶ M b := by
  subst b
  exact 𝟙 _

private theorem groupOrderHom_intCast {a b : ℕ} (h : a = b) (z : ℤ) :
    groupOrderHom h (z : ZMod a) = (z : ZMod b) := by
  subst b
  rfl

private theorem residueArrow_factor (r : ℕ) :
    groupOrderHom (pow_succ ℓ r) ≫
      AddCommGrpCat.ofHom (ZModReductionSequence.reduction (ℓ ^ r) ℓ).toAddMonoidHom =
    residueArrow ℓ r := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  obtain ⟨z, rfl⟩ := ZMod.intCast_surjective x
  change ZModReductionSequence.reduction (ℓ ^ r) ℓ
      (groupOrderHom (pow_succ ℓ r) (z : ZMod (ℓ ^ (r + 1)))) =
    PadicResidueSystems.reduction ℓ (Nat.le_succ r) (z : ZMod (ℓ ^ (r + 1)))
  rw [groupOrderHom_intCast, map_intCast, map_intCast]

variable {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]

private def sheafOrderHom {a b : ℕ} (h : a = b) : coefficients j a ⟶ coefficients j b := by
  subst b
  exact 𝟙 _

private theorem groupOrderHom_map {a b : ℕ} (h : a = b) :
    (extendedConstants j).map (groupOrderHom h) = sheafOrderHom j h := by
  subst b
  exact (extendedConstants j).map_id _

/-- Actual coefficient transition on the classical compact model is the
extended-constant image of the actual residue ring homomorphism. -/
theorem coefficientTransition_eq_map (r : ℕ) :
    coefficientTransition j ℓ r = (extendedConstants j).map (residueArrow ℓ r) := by
  change sheafOrderHom j (pow_succ ℓ r) ≫
      (extendedConstants j).map
        (AddCommGrpCat.ofHom (ZModReductionSequence.reduction (ℓ ^ r) ℓ).toAddMonoidHom) =
    (extendedConstants j).map (residueArrow ℓ r)
  rw [← groupOrderHom_map, ← Functor.map_comp, residueArrow_factor]

end
end ManuscriptAudit.OpenEtalePrimeTowerArrow

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.OpenEtalePrimeTowerArrow.residueArrow,
      ``ManuscriptAudit.OpenEtalePrimeTowerArrow.coefficientTransition_eq_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
