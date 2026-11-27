import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffineClosedPoints
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicardTorsion

/-!
# Points and the actual affine Picard group over the algebraic closure

A closed-point ideal is invertible. Dividing an invertible integral
ideal by a containing closed-point ideal strictly increases it in
the noetherian order. This expresses its class as a sum of point
classes. Clearing denominators then supplies every Picard class.
-/

namespace ManuscriptAudit.WeierstrassAffinePicard

open FractionalIdeal Polynomial WeierstrassCurve.Affine
open scoped nonZeroDivisors
open WeierstrassAffineClosedPoints WeierstrassAffinePicardTorsion

noncomputable section

variable {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev R := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev FI := FractionalIdeal (R W)⁰ (F W)

private theorem integralClass_is_point (I : Ideal (R W)) (u : (FI W)ˣ)
    (hu : (u : FI W) = (I : FI W)) :
    ∃ P : W.Point, Point.toClass P = Additive.ofMul (ClassGroup.mk (F W) u) := by
  letI : IsNoetherianRing (R W) := inferInstanceAs
    (IsNoetherianRing (AdjoinRoot W.polynomial))
  have wf : WellFounded ((· > ·) : Ideal (R W) → Ideal (R W) → Prop) :=
    (isNoetherian_iff (R := R W) (M := R W)).mp inferInstance
  revert u
  refine wf.induction I ?_
  clear I
  intro I ih u hu
  by_cases hI : I = ⊤
  · have hU : u = 1 := by
      apply Units.ext
      rw [hu, hI, coeIdeal_top] <;> rfl
    refine ⟨0, ?_⟩
    rw [hU, map_one, Point.toClass_zero] <;> rfl
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨x, y, hxy, hMpoint⟩ := maximalIdeal_is_point W M hM
  have hn : W.Nonsingular x y := (equation_iff_nonsingular (W := W)).mp hxy
  let m := CoordinateRing.XYIdeal' hn
  have hm : (m : FI W) = (M : FI W) := by
    rw [hMpoint, CoordinateRing.XYIdeal'_eq]
  let v := m⁻¹ * u
  have hmv : m * v = u := by
    change m * (m⁻¹ * u) = u
    rw [← mul_assoc, mul_inv_cancel, one_mul]
  have hLe : (u : FI W) ≤ (m : FI W) := by
    rw [hu, hm, coeIdeal_le_coeIdeal]
    exact hIM
  have hInt : (v : FI W) ≤ 1 := calc
    (v : FI W) = (↑(m⁻¹) : FI W) * (u : FI W) := rfl
    _ ≤ (↑(m⁻¹) : FI W) * (m : FI W) := mul_left_mono hLe
    _ = 1 := by rw [← Units.val_mul, inv_mul_cancel] <;> rfl
  obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hInt
  have hIJmul : I = M * J := by
    apply coeIdeal_injective (K := F W)
    rw [coeIdeal_mul, hJ, ← hm, ← Units.val_mul, hmv, hu]
  have hIJ : I ≤ J := by
    rw [hIJmul]
    exact Ideal.mul_le_left
  have hStrict : I < J := lt_of_le_of_ne hIJ (fun he => by
    have hvu : v = u := Units.ext (calc
      (v : FI W) = (J : FI W) := hJ.symm
      _ = (I : FI W) := congrArg (fun L : Ideal (R W) => (L : FI W)) he.symm
      _ = (u : FI W) := hu.symm)
    have hmOne : m = 1 := mul_right_cancel (show m * u = 1 * u by
      simpa only [hvu, one_mul] using hmv)
    apply hM.ne_top
    apply coeIdeal_injective (K := F W)
    rw [← hm, hmOne, coeIdeal_top] <;> rfl)
  obtain ⟨P, hP⟩ := ih J hStrict v hJ.symm
  refine ⟨Point.some x y hn + P, ?_⟩
  rw [map_add, Point.toClass_some, hP]
  change ClassGroup.mk (F W) m * ClassGroup.mk (F W) v = ClassGroup.mk (F W) u
  rw [← map_mul, hmv]

/-- The native point-to-class map is onto for the geometric smooth affine chart. -/
theorem pointToClass_surjective : Function.Surjective (Point.toClass (W := W)) := by
  have hSurj : Function.Surjective
      (ClassGroup.mk (F W) : (FI W)ˣ → ClassGroup (R W)) := by
    rintro ⟨u⟩
    exact ⟨u, (ClassGroup.Quot_mk_eq_mk u).symm⟩
  intro c
  obtain ⟨u, hu⟩ := hSurj c.toMul
  have hd : algebraMap (R W) (F W) u.val.den ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors u.val.den.property
  let a : (F W)ˣ := Units.mk0 (algebraMap (R W) (F W) u.val.den) hd
  let v := u * toPrincipalIdeal (R W) (F W) a
  have hv : (v : FI W) = (u.val.num : FI W) := by
    change (u : FI W) * (toPrincipalIdeal (R W) (F W) a : FI W) = _
    rw [coe_toPrincipalIdeal, mul_comm]
    exact den_mul_self_eq_num' (R W)⁰ (F W) (u : FI W)
  obtain ⟨P, hP⟩ := integralClass_is_point W u.val.num v hv
  have hClasses : ClassGroup.mk (F W) u = ClassGroup.mk (F W) v :=
    ClassGroup.mk_eq_mk.mpr ⟨a, rfl⟩
  exact ⟨P, hP.trans (congrArg Additive.ofMul (hClasses.symm.trans hu))⟩

/-- The elliptic point group is isomorphic to the invertible-module Picard
group of its geometric affine coordinate ring. -/
def pointPicardEquiv : W.Point ≃+ Additive (CommRing.Pic (R W)) :=
  AddEquiv.ofBijective (pointToPicard W)
    ⟨pointToPicard_injective W,
      (ClassGroup.equivPic (R W)).toAdditive.surjective.comp (pointToClass_surjective W)⟩

/-- The true affine Picard Tate module is isomorphic to the geometric point Tate module. -/
def tatePicardEquiv (l : ℕ) [Fact l.Prime] :
    PowerTateModule.Tate l W.Point ≃ₗ[ℤ_[l]]
      PowerTateModule.Tate l (Additive (CommRing.Pic (R W))) :=
  PowerTateModule.mapAddEquiv l (pointPicardEquiv W)

end

end ManuscriptAudit.WeierstrassAffinePicard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffinePicard.pointToClass_surjective,
      ``ManuscriptAudit.WeierstrassAffinePicard.pointPicardEquiv,
      ``ManuscriptAudit.WeierstrassAffinePicard.tatePicardEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
