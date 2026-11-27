import Lean.Util.CollectAxioms
import Mathlib.Algebra.Group.Subgroup.Map
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerDifference
import PrimalitySheafVerification.ManuscriptAudit.SequentialInverseLimitDifference
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit

/-! The categorical abelian-group product difference and its concrete compatible classes. -/

namespace ManuscriptAudit.AbProductDifference

open CategoryTheory CategoryTheory.Limits
open ComplexTowerDifference (difference difference_π)
open SequentialInverseLimitDifference
open CyclicPowerInverseLimit (compatibleTuples)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}

variable (G : ℕ → A) (transition : ∀ r, G (r + 1) ⟶ G r)

/-- The categorical product is the group of dependent tuples. -/
def productIso : ∏ᶜ G ≅ AddCommGrpCat.of (∀ r, G r) :=
  (limit.isLimit _).conePointUniqueUpToIso (AddCommGrpCat.HasLimit.productLimitCone G).isLimit

private theorem productIso_apply (x : (∏ᶜ G : A)) (r : ℕ) :
    (productIso G).hom x r = Pi.π G r x :=
  CategoryTheory.congr_fun (IsLimit.conePointUniqueUpToIso_hom_comp
    (limit.isLimit _) (AddCommGrpCat.HasLimit.productLimitCone G).isLimit (Discrete.mk r)) x

/-- The coordinatewise consecutive difference, bundled as an abelian-group morphism. -/
def concreteDifference : AddCommGrpCat.of (∀ r, G r) ⟶ AddCommGrpCat.of (∀ r, G r) :=
  AddCommGrpCat.ofHom (productDifference (fun r ↦ G r) (fun r ↦ (transition r).hom))

/-- The canonical product comparison intertwines the categorical and concrete differences. -/
theorem difference_comp_productIso :
    difference G transition ≫ (productIso G).hom =
      (productIso G).hom ≫ concreteDifference G transition := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  funext r
  change (productIso G).hom (difference G transition x) r =
    (productIso G).hom x r - transition r ((productIso G).hom x (r + 1))
  simp only [productIso_apply]
  exact CategoryTheory.congr_fun (difference_π G transition r) x

/-- Surjectivity of every transition makes the categorical difference an epimorphism. -/
theorem difference_epi (onto : ∀ r, Function.Surjective (transition r : G (r + 1) → G r)) :
    Epi (difference G transition) := by
  letI : Epi (concreteDifference G transition) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (productDifference_surjective (fun r ↦ G r) (fun r ↦ (transition r).hom) onto)
  have h : Epi ((productIso G).hom ≫ concreteDifference G transition) := inferInstance
  rw [← difference_comp_productIso] at h
  letI := h
  exact epi_of_epi (difference G transition) (productIso G).hom

private theorem concrete_kernel :
    (concreteDifference G transition).hom.ker =
      compatibleTuples (fun r ↦ G r) (fun r ↦ (transition r).hom) := by
  ext x
  exact productDifference_eq_zero_iff (fun r ↦ G r) (fun r ↦ (transition r).hom) x

/-- The native categorical kernel is exactly the compatible-class group. -/
def kernelEquiv : (kernel (difference G transition) : A) ≃+
    compatibleTuples (fun r ↦ G r) (fun r ↦ (transition r).hom) := by
  let g := concreteDifference G transition
  let e := productIso G
  let k := kernel.mapIso (difference G transition) g e e (difference_comp_productIso G transition)
  let m := (k ≪≫ AddCommGrpCat.kernelIsoKer g).addCommGroupIsoToAddEquiv
  let h : g.hom.ker = compatibleTuples (fun r ↦ G r) (fun r ↦ (transition r).hom) :=
    concrete_kernel G transition
  exact m.trans (AddEquiv.addSubgroupCongr h)

end
end ManuscriptAudit.AbProductDifference

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AbProductDifference.productIso,
      ``ManuscriptAudit.AbProductDifference.difference_comp_productIso,
      ``ManuscriptAudit.AbProductDifference.difference_epi,
      ``ManuscriptAudit.AbProductDifference.kernelEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
