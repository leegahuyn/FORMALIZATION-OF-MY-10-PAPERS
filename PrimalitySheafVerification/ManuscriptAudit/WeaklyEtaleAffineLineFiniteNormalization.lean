import Lean.Util.CollectAxioms
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral
import Mathlib.Algebra.Polynomial.FieldDivision
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineGenericStage

/-! A finite étale generic stage has a finite product of Dedekind
normalizations, with a map to the actual affine-line chart. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)
open WeaklyEtaleAffineLineGenericStage (F genericFibre inclusion)
open scoped nonZeroDivisors TensorProduct

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable (K B : Type u) [Field K] [IsAlgClosed K] [CommRing B] [Algebra (Polynomial K) B]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

variable {ι : Type u} (L : ι → Type u) [Finite ι]
  [∀ i, Field (L i)] [∀ i, Algebra (F K) (L i)]
  [∀ i, Algebra (R K) (L i)] [∀ i, IsScalarTower (R K) (F K) (L i)]
  [∀ i, Module.Finite (F K) (L i)] [∀ i, Algebra.IsSeparable (F K) (L i)]

abbrev model := ∀ i, integralClosure (R K) (L i)

def modelInclusion : model K L →ₐ[R K] (∀ i, L i) :=
  AlgHom.pi fun i ↦ (integralClosure (R K) (L i)).val.comp
    (Pi.evalAlgHom (R K) (fun j ↦ integralClosure (R K) (L j)) i)

theorem modelInclusion_injective : Function.Injective (modelInclusion K L) := by
  intro x y h
  funext i
  exact Subtype.ext (congrFun h i)

theorem model_finite : Module.Finite (R K) (model K L) := by
  letI (i : ι) : Module.Finite (R K) (integralClosure (R K) (L i)) :=
    IsIntegralClosure.finite (R K) (F K) (L i) (integralClosure (R K) (L i))
  infer_instance

theorem component_dedekind (i : ι) : IsDedekindDomain (integralClosure (R K) (L i)) :=
  integralClosure.isDedekindDomain (R K) (F K) (L i)

variable {E : Type u} [CommRing E] [Algebra (R K) E] [Algebra (F K) E]
  [IsScalarTower (R K) (F K) E] [Module.Finite (F K) E]

/-- For a field-product presentation of a generic stage, the product
of its integral closures maps to the actual weakly étale chart.
Every element of the generic stage has a nonzero scalar multiple
from that normal model. -/
theorem exists_model_map (e : E ≃ₐ[F K] (∀ i, L i))
    (f : E →ₐ[R K] genericFibre K B) (hf : Function.Injective f) :
    ∃ g : model K L →ₐ[R K] B, Function.Injective g ∧
      (inclusion K B).comp g =
        (f.comp (e.symm.toAlgHom.restrictScalars (R K))).comp (modelInclusion K L) ∧
      ∀ x : E, ∃ (a : (R K)⁰) (d : model K L),
        inclusion K B (g d) = f (a • x) := by
  let j := f.comp (e.symm.toAlgHom.restrictScalars (R K))
  let h := j.comp (modelInclusion K L)
  letI : Module.Finite (R K) (model K L) := model_finite K L
  obtain ⟨g, hg, _⟩ := WeaklyEtaleAffineLineGenericStage.existsUnique_integral_lift
    K B (fun x ↦ IsIntegral.of_finite (R K) x) h
  have hgi : Function.Injective g := by
    intro x y hxy
    have hx : h x = h y := by
      rw [← hg, AlgHom.comp_apply, AlgHom.comp_apply, hxy]
    exact (hf.comp (e.symm.injective.comp (modelInclusion_injective K L))) hx
  refine ⟨g, hgi, hg, fun x ↦ ?_⟩
  obtain ⟨a, ha⟩ := IsIntegral.exists_multiple_integral_of_isLocalization (R K)⁰ x
    (IsIntegral.of_finite (F K) x)
  have hCoord (i : ι) : IsIntegral (R K) (e (a • x) i) :=
    ha.map ((Pi.evalAlgHom (F K) L i).comp e.toAlgHom)
  let d : model K L := fun i ↦ ⟨e (a • x) i, (mem_integralClosure_iff (R K) (L i)).mpr (hCoord i)⟩
  refine ⟨a, d, ?_⟩
  change ((inclusion K B).comp g) d = _
  rw [hg]
  change f (e.symm (e (a • x))) = _
  rw [e.symm_apply_apply]

end
end ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization.model_finite,
      ``ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization.component_dedekind,
      ``ManuscriptAudit.WeaklyEtaleAffineLineFiniteNormalization.exists_model_map] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
