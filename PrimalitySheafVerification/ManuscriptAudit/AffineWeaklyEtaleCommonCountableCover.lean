import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCommonCountableCover
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleFlatIncreasingUnion

/-! A countable family of faithfully flat weakly étale affine covers has an actual common cover. -/

namespace ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
open AffineEtaleTensorStages (stage)
open AffineEtaleTensorDirectLimit
  (Tower Stage stageMap stageMap_injective stageMap_transition transition exists_stage)
open AffineEtaleCommonCountableCover (coverMap factorMap factor_comp)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (B : ℕ → CommAlgCat.{0} R)
variable (hFaithful : ∀ n, Module.FaithfullyFlat R (B n))
variable (hWeak : ∀ n, WeaklyEtale (ProetaleAffineTensor.structureMap R (B n)))

include hWeak in
theorem stage_weaklyEtale (n : ℕ) :
    WeaklyEtale (ProetaleAffineTensor.structureMap R (stage B n)) := by
  induction n with
  | zero =>
    change WeaklyEtale (Spec.map (CommRingCat.ofHom (algebraMap R R)))
    have h : CommRingCat.ofHom (algebraMap R R) = 𝟙 (CommRingCat.of R) := by
      apply CommRingCat.hom_ext
      exact RingHom.ext fun _ => rfl
    rw [h, Spec.map_id]
    infer_instance
  | succ n ih =>
    letI : WeaklyEtale (ProetaleAffineTensor.structureMap R (stage B n)) := ih
    letI : WeaklyEtale (ProetaleAffineTensor.structureMap R (B n)) := hWeak n
    change WeaklyEtale (ProetaleAffineTensor.structureMap R ((stage B n) ⊗[R] (B n)))
    infer_instance

private def stages (n : ℕ) : Subalgebra R (Tower B) := (stageMap B n).range

private theorem stages_monotone : Monotone (stages B) := by
  intro n m h x hx
  obtain ⟨z, rfl⟩ := hx
  exact ⟨transition B n m h z, stageMap_transition B h z⟩

private theorem stages_exhaustive (x : Tower B) : ∃ n, x ∈ stages B n := by
  obtain ⟨n, z, hz⟩ := exists_stage B x
  exact ⟨n, z, hz⟩

include hFaithful hWeak in
private theorem rangeStage_weaklyEtale (n : ℕ) :
    WeaklyEtale (ProetaleAffineTensor.structureMap R (stages B n)) := by
  let e : Stage B n ≃ₐ[R] stages B n :=
    AlgEquiv.ofInjective (stageMap B n) (stageMap_injective B hFaithful n)
  letI : WeaklyEtale (ProetaleAffineTensor.structureMap R (Stage B n)) :=
    stage_weaklyEtale B hWeak n
  letI : IsIso (ProetaleAffineTensor.specMap R e.toAlgHom) := by
    change IsIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom)
    infer_instance
  rw [← ProetaleAffineTensor.specMap_structureMap R e.toAlgHom]
  infer_instance

include hFaithful hWeak in
theorem cover_weaklyEtale : WeaklyEtale (coverMap B) :=
  WeaklyEtaleFlatIncreasingUnion.weaklyEtale (stages B) (stages_monotone B) (stages_exhaustive B)
    (rangeStage_weaklyEtale B hFaithful hWeak)

include hFaithful hWeak in
theorem exists_common_cover :
    ∃ f : Spec (CommRingCat.of (Tower B)) ⟶ Spec (CommRingCat.of R),
      WeaklyEtale f ∧ Surjective f ∧
      ∀ n, factorMap B n ≫ ProetaleAffineTensor.structureMap R (B n) = f :=
  ⟨coverMap B, cover_weaklyEtale B hFaithful hWeak,
    AffineEtaleCommonCountableCover.cover_surjective B hFaithful, factor_comp B⟩

end
end ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover.stage_weaklyEtale,
      ``ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover.cover_weaklyEtale,
      ``ManuscriptAudit.AffineWeaklyEtaleCommonCountableCover.exists_common_cover] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
