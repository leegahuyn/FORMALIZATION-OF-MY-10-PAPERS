import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Unramified.LocalRing
import PrimalitySheafVerification.ManuscriptAudit.DVRParameterReduction
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleAffineLineLocalReducedFibres

/-! A normal finite-type stage under a weakly étale affine-line chart
is unramified at each closed image with separable residue extension. -/

namespace ManuscriptAudit.WeaklyEtaleAffineLineStageUnramified

open AlgebraicGeometry CategoryTheory
open ProetaleAffineTensor (structureMap)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {K C B : Type u} [Field K] [IsAlgClosed K] [CommRing C] [CommRing B]
  [Algebra (Polynomial K) C] [Algebra (Polynomial K) B]
  [Algebra.EssFiniteType (Polynomial K) C] [WeaklyEtale (structureMap (Polynomial K) B)]

private abbrev R := Polynomial K

private theorem scalar_nonzero_localization (r : Ideal B) [r.IsPrime] (t : R) (ht : t ≠ 0) :
    algebraMap B (Localization.AtPrime r) (algebraMap (R (K := K)) B t) ≠ 0 := by
  let A := R (K := K)
  let D := Localization.AtPrime r
  let φ := CommRingCat.ofHom (algebraMap A B)
  letI : Module.Flat A B := (RingHom.flat_algebraMap_iff).mp
    ((Flat.SpecMap_iff (f := φ)).mp (inferInstanceAs (Flat (structureMap A B))))
  letI : Module.Flat A D := Module.Flat.trans A B D
  have hReg : IsSMulRegular D t :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ht)
  intro h
  have he : t • (1 : D) = t • (0 : D) := by
    rw [Algebra.smul_def, mul_one, smul_zero, IsScalarTower.algebraMap_apply A B D]
    exact h
  exact one_ne_zero (hReg he)

set_option maxHeartbeats 1900000 in
/-- At a closed image, the stage parameter has ramification exponent
one, using exactly the actual reduced fibre of the dominating chart. -/
theorem isUnramifiedAt (g : C →ₐ[Polynomial K] B)
    (p : Ideal (Polynomial K)) [p.IsPrime] (q : Ideal C) [q.IsPrime] [q.LiesOver p]
    (r : Ideal B) [r.IsPrime] (hqr : q = r.comap g.toRingHom)
    [IsDiscreteValuationRing (Localization.AtPrime q)]
    (t : Polynomial K) (ht : Prime t) (hp : p = Ideal.span ({t} : Set (Polynomial K)))
    (hSep : Algebra.IsSeparable p.ResidueField q.ResidueField) :
    Algebra.IsUnramifiedAt (Polynomial K) q := by
  let A := Polynomial K
  let S := Localization.AtPrime q
  let T := Localization.AtPrime r
  let f : S →+* T := Localization.localRingHom q r g.toRingHom hqr
  letI : IsLocalHom f := inferInstanceAs (IsLocalHom (Localization.localRingHom q r g.toRingHom hqr))
  let s := algebraMap A S t
  have hpt : t ∈ p := by
    rw [hp]
    exact Ideal.subset_span (by simp)
  have hq : algebraMap A C t ∈ q := by
    change t ∈ q.comap (algebraMap A C)
    rwa [← q.over_def p]
  have hs : s ∈ IsLocalRing.maximalIdeal S := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    change algebraMap A S t ∈ q.map (algebraMap C S)
    rw [IsScalarTower.algebraMap_apply A C S]
    exact Ideal.mem_map_of_mem _ hq
  have hfs : f s = algebraMap B T (algebraMap A B t) := by
    change Localization.localRingHom q r g.toRingHom hqr (algebraMap A S t) = _
    rw [IsScalarTower.algebraMap_apply A C S, Localization.localRingHom_to_map]
    exact congrArg (algebraMap B T) (g.commutes t)
  have hfs₀ : f s ≠ 0 := by
    rw [hfs]
    exact scalar_nonzero_localization r t ht.ne_zero
  letI : IsReduced (T ⧸ Ideal.span ({f s} : Set T)) := by
    rw [hfs]
    exact WeaklyEtaleAffineLineLocalReducedFibres.reduced_atPrime K B t ht r
  have hm := DVRParameterReduction.maximalIdeal_eq_span_of_reduced_image f s hs hfs₀
  apply (Algebra.isUnramifiedAt_iff_map_eq A p q).mpr
  refine ⟨hSep, ?_⟩
  rw [hp, Ideal.map_span, Set.image_singleton]
  exact hm.symm

end
end ManuscriptAudit.WeaklyEtaleAffineLineStageUnramified

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.WeaklyEtaleAffineLineStageUnramified.isUnramifiedAt
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
