import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorDirectLimit
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleIncreasingUnion
import PrimalitySheafVerification.ManuscriptAudit.FaithfullyFlatIncreasingUnion

/-! A countable sequence of faithfully flat étale affine covers has a
single genuine affine weakly étale surjective chart factoring through each. -/

namespace ManuscriptAudit.AffineEtaleCommonCountableCover

open AlgebraicGeometry CategoryTheory
open AffineEtaleTensorStages (stage_etale stage_faithfullyFlat factor)
open AffineEtaleTensorDirectLimit (Tower stageMap stageMap_injective stageMap_transition transition exists_stage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (B : ℕ → CommAlgCat.{0} R)
variable (hF : ∀ n, Module.FaithfullyFlat R (B n))
variable (hE : ∀ n, Algebra.Etale R (B n))

private def U (n : ℕ) : Subalgebra R (Tower B) := (stageMap B n).range

private def stageEquiv (n : ℕ) : AffineEtaleTensorDirectLimit.Stage B n ≃ₐ[R] U B n :=
  AlgEquiv.ofInjective (stageMap B n) (stageMap_injective B hF n)

private theorem U_mono : Monotone (U B) := by
  intro n m h x hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨transition B n m h z, stageMap_transition B h z⟩

private theorem U_cover (x : Tower B) : ∃ n, x ∈ U B n := by
  obtain ⟨n, z, hz⟩ := exists_stage B x
  exact ⟨n, z, hz⟩

include hF in
private theorem U_faithfullyFlat (n : ℕ) : Module.FaithfullyFlat R (U B n) := by
  letI := stage_faithfullyFlat B hF n
  exact Module.FaithfullyFlat.of_linearEquiv ((stageEquiv B hF n).symm.toLinearEquiv)

include hF hE in
private theorem U_etale (n : ℕ) : Algebra.Etale R (U B n) := by
  letI := stage_etale B hE n
  exact Algebra.Etale.of_equiv (stageEquiv B hF n)

/-- The actual affine countable refinement over the base spectrum. -/
abbrev coverMap : Spec (CommRingCat.of (Tower B)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Tower B)))

include hF hE in
theorem cover_weaklyEtale : WeaklyEtale (coverMap B) :=
  WeaklyEtaleIncreasingUnion.weaklyEtale (U B) (U_mono B) (U_cover B) (U_etale B hF hE)

include hF in
theorem cover_surjective : Surjective (coverMap B) := by
  letI : Module.FaithfullyFlat R (Tower B) :=
    FaithfullyFlatIncreasingUnion.faithfullyFlat (U B) (U_mono B) (U_cover B) (U_faithfullyFlat B hF)
  rw [AlgebraicGeometry.surjective_iff]
  exact PrimeSpectrum.comap_surjective_of_faithfullyFlat

private def factorAlg (n : ℕ) : B n →ₐ[R] Tower B :=
  (stageMap B (n + 1)).comp (factor B n).hom

/-- The countable refinement maps through each original scheme cover. -/
def factorMap (n : ℕ) : Spec (CommRingCat.of (Tower B)) ⟶ Spec (CommRingCat.of (B n)) :=
  Spec.map (CommRingCat.ofHom (factorAlg B n).toRingHom)

theorem factor_comp (n : ℕ) :
    factorMap B n ≫ Spec.map (CommRingCat.ofHom (algebraMap R (B n))) = coverMap B := by
  rw [factorMap, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact RingHom.ext (factorAlg B n).commutes

end

end ManuscriptAudit.AffineEtaleCommonCountableCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleCommonCountableCover.cover_weaklyEtale,
      ``ManuscriptAudit.AffineEtaleCommonCountableCover.cover_surjective,
      ``ManuscriptAudit.AffineEtaleCommonCountableCover.factor_comp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
