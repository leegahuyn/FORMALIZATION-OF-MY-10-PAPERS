import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import PrimalitySheafVerification.ManuscriptAudit.ValuationLocalDivision
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineLocalReducedFibres

/-! Elements of the actual affine line chart with a denominator in a
normal stage have no pole at the image of an actual chart point. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineLocalExtension

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K B D : Type u} [Field K] [CommRing B] [CommRing D]
  [Algebra (Polynomial K) B] [Algebra (Polynomial K) D]
  [WeaklyEtale (structureMap (Polynomial K) B)]

private theorem regular_scalar (r : Ideal B) [r.IsPrime] (a : Polynomial K) (ha : a ≠ 0) :
    IsRegular (algebraMap (Polynomial K) (Localization.AtPrime r) a) := by
  let A := Polynomial K
  let T := Localization.AtPrime r
  let φ := CommRingCat.ofHom (algebraMap A B)
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp
    ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat (structureMap A B))))
  letI : Module.Flat A T := Module.Flat.trans A B T
  have h : IsSMulRegular T a := Module.Flat.isSMulRegular_of_nonZeroDivisors
    (mem_nonZeroDivisors_of_ne_zero ha)
  have hl : IsLeftRegular (algebraMap A T a) := by
    intro x y e
    apply h
    simpa only [Algebra.smul_def] using e
  exact ⟨hl, fun _ _ e ↦ hl (by simpa only [mul_comm] using e)⟩

/-- A section realized as a fraction of elements at a normal finite
stage is already regular in the actual valuation stalk of that stage
at every image point of the weakly étale chart. -/
theorem exists_local_preimage (g : D →ₐ[Polynomial K] B)
    (r : Ideal B) [r.IsPrime] (q : Ideal D) [q.IsPrime]
    (hqr : q = r.comap g.toRingHom)
    [IsDomain (Localization.AtPrime q)] [ValuationRing (Localization.AtPrime q)]
    (a : Polynomial K) (ha : a ≠ 0) (b : D) (z : B)
    (h : g b = algebraMap (Polynomial K) B a * z) :
    ∃ d : Localization.AtPrime q,
      Localization.localRingHom q r g.toRingHom hqr d = algebraMap B (Localization.AtPrime r) z := by
  let A := Polynomial K
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  let f : S →+* T := Localization.localRingHom q r g.toRingHom hqr
  letI : IsLocalHom f :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom q r g.toRingHom hqr))
  let a' := algebraMap A S a
  have hfa : f a' = algebraMap A T a := by
    change Localization.localRingHom q r g.toRingHom hqr (algebraMap A S a) = _
    rw [IsScalarTower.algebraMap_apply A D S, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply A B T]
    exact congrArg (algebraMap B T) (g.commutes a)
  have he : f (algebraMap D S b) = f a' * algebraMap B T z := by
    rw [hfa, IsScalarTower.algebraMap_apply A B T]
    change Localization.localRingHom q r g.toRingHom hqr (algebraMap D S b) = _
    rw [Localization.localRingHom_to_map, h, map_mul]
  have hr : IsRegular (f a') := hfa.symm ▸ regular_scalar r a ha
  obtain ⟨d, _, hd⟩ := ValuationLocalDivision.exists_quotient f hr he
  exact ⟨d, hd⟩

end
end ManuscriptAudit.WeaklyEtaleAffineLineLocalExtension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineLocalExtension.exists_local_preimage
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
