import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineGenericIntegral
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleFieldFiniteStages

/-! The actual generic fibre admits finite étale stages. Integral
models of these generic stages already map to the original chart. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineGenericStage

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap specMap leftInclusion specTensor_isPullback)
open WeaklyEtaleAffineLineGenericIntegral (denominators genericRing genericMap_injective)
open scoped TensorProduct nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K
abbrev F := FractionRing (R K)
abbrev genericFibre := F K ⊗[R K] B

attribute [local instance] Algebra.TensorProduct.rightAlgebra

private theorem fibre_weaklyEtale : WeaklyEtale (structureMap (F K) (genericFibre K B)) := by
  change WeaklyEtale (specMap (R K) (leftInclusion (R K) (F K) B))
  exact MorphismProperty.of_isPullback (P := @WeaklyEtale)
    (specTensor_isPullback (R K) (F K) B).flip
      (inferInstanceAs (WeaklyEtale (structureMap (R K) B)))

/-- A finite set of actual generic sections is contained in its
finitely generated finite étale subalgebra. -/
theorem adjoin_finite_etale (s : Set (genericFibre K B)) (hs : s.Finite) :
    Module.Finite (F K) (Algebra.adjoin (F K) s) ∧
      Algebra.Etale (F K) (Algebra.adjoin (F K) s) := by
  letI : WeaklyEtale (structureMap (F K) (genericFibre K B)) := fibre_weaklyEtale K B
  exact WeaklyEtaleFieldFiniteStages.adjoin_finite_etale (F K) (genericFibre K B) s hs

/-- The actual chart embeds into the tensor product describing its generic fibre. -/
abbrev inclusion : B →ₐ[R K] genericFibre K B := Algebra.TensorProduct.includeRight

private def genericEquiv : genericRing K B ≃ₐ[B] genericFibre K B :=
  IsLocalization.algEquiv (denominators K B) _ _

private theorem genericEquiv_apply_algebraMap (b : B) :
    genericEquiv K B (algebraMap B (genericRing K B) b) = inclusion K B b := by
  rw [(genericEquiv K B).commutes, Algebra.TensorProduct.right_algebraMap_apply]
  exact (Algebra.TensorProduct.includeRight_apply b).symm

theorem inclusion_injective : Function.Injective (inclusion K B) := by
  intro b d h
  apply genericMap_injective K B
  apply (genericEquiv K B).injective
  rw [genericEquiv_apply_algebraMap K B b, genericEquiv_apply_algebraMap K B d]
  exact h

private theorem inclusion_of_integral (x : genericFibre K B) (hx : IsIntegral (R K) x) :
    x ∈ (inclusion K B).range := by
  let e := genericEquiv K B
  have h' : IsIntegral B (e.symm x) := (hx.tower_top (A := B)).map e.symm
  obtain ⟨b, hb⟩ := WeaklyEtaleAffineLineGenericIntegral.exists_of_integral K B (e.symm x) h'
  refine ⟨b, ?_⟩
  change inclusion K B b = x
  calc
    _ = e (algebraMap B (genericRing K B) b) := (genericEquiv_apply_algebraMap K B b).symm
    _ = _ := by rw [hb, e.apply_symm_apply]

set_option maxHeartbeats 1800000 in
/-- Any integral model inside the genuine generic fibre has a unique
algebra map to the actual weakly étale chart, compatible with the generic map. -/
theorem existsUnique_integral_lift {D : Type u} [CommRing D] [Algebra (R K) D]
    (hD : ∀ d : D, IsIntegral (R K) d) (f : D →ₐ[R K] genericFibre K B) :
    ∃! g : D →ₐ[R K] B, (inclusion K B).comp g = f := by
  let j := inclusion K B
  let j' := j.codRestrict j.range (fun b ↦ ⟨b, rfl⟩)
  have hj' : Function.Bijective j' := by
    refine ⟨fun _ _ h ↦ inclusion_injective K B (congrArg Subtype.val h), ?_⟩
    rintro ⟨x, hx⟩
    obtain ⟨b, hb⟩ := hx
    exact ⟨b, Subtype.ext hb⟩
  let e := AlgEquiv.ofBijective j' hj'
  let f' := f.codRestrict j.range (fun d ↦ inclusion_of_integral K B (f d) ((hD d).map f))
  let g := e.symm.toAlgHom.comp f'
  have hg : j.comp g = f := by
    ext d
    change j (e.symm (f' d)) = f d
    exact congrArg Subtype.val (e.apply_symm_apply (f' d))
  refine ⟨g, hg, fun g' hg' ↦ ?_⟩
  apply AlgHom.ext
  intro d
  apply inclusion_injective K B
  exact DFunLike.congr_fun (hg'.trans hg.symm) d

end
end ManuscriptAudit.WeaklyEtaleAffineLineGenericStage

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAffineLineGenericStage.adjoin_finite_etale,
      ``ManuscriptAudit.WeaklyEtaleAffineLineGenericStage.inclusion_injective,
      ``ManuscriptAudit.WeaklyEtaleAffineLineGenericStage.existsUnique_integral_lift] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
