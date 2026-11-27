import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionKernel
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionAlgebra

/-! The finite points of actual nineteen-torsion have the three certified abscissa cubes. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinates

open WeierstrassCurve CubicThreeTorsionOrdinate CubicTwoTorsion CubicThreeTorsion CubicTriplingCoordinates
open Paper5OrdinaryNineteenAlgebra Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenSecant
open Paper5OrdinaryNineteenTorsionAlgebra Paper5OrdinaryNineteenTorsionKernel

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

private theorem rotation_cube_apply (P : Points L) :
    rotation L (rotation L (rotation L P)) = P :=
  CubicCubeRotation.rotate_cube rotation_cube (discriminant_ne_zero L) P

private def singleDoubleX (x : L) : L :=
  x * (singleRotatedDoubleNumerator (x ^ 3) / doubleDenominator (x ^ 3))

private def positiveDoubleY (x y : L) : L :=
  y * (doubleOrdinateNumerator (x ^ 3) / doubleOrdinateDenominator (x ^ 3))

private theorem singleDoubleX_eq (x : L) :
    (7 : L) * (7 * doubleX x) = singleDoubleX L x := by
  unfold doubleX singleDoubleX
  calc
    _ = x * (((7 : L) ^ 2 * rotatedDoubleNumerator (x ^ 3)) / doubleDenominator (x ^ 3)) := by ring
    _ = _ := by rw [rotation_square, rotation_square_times_double]

set_option maxHeartbeats 800000 in
private theorem rotated_double_some {x y : L} (hP : (Curve (1 : L)).Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : (Curve (1 : L)).Nonsingular (singleDoubleX L x) (positiveDoubleY L x y),
      (2 : ℕ) • rotation L (Affine.Point.some x y hP) =
        Affine.Point.some (singleDoubleX L x) (positiveDoubleY L x y) h' := by
  obtain ⟨hD, eD⟩ := minus_rotated_double_some L hP hy
  obtain ⟨hR, eR⟩ := rotation_some L hD
  obtain ⟨hR', eR'⟩ := rotation_some L hR
  let P : Points L := Affine.Point.some x y hP
  let xn := 7 * (7 * doubleX x)
  let yn := minusDoubleY x y
  have eX : xn = singleDoubleX L x := singleDoubleX_eq L x
  have eY : (Curve (1 : L)).negY xn yn = positiveDoubleY L x y := by
    rw [negY_eq]
    unfold yn positiveDoubleY minusDoubleY
    ring
  have hN : (Curve (1 : L)).Nonsingular xn ((Curve (1 : L)).negY xn yn) :=
    (Affine.nonsingular_neg ..).mpr hR'
  refine ⟨by simpa only [← eX, ← eY] using hN, ?_⟩
  change (2 : ℕ) • rotation L P = _
  calc
    _ = -rotation L (rotation L (-((2 : ℕ) • rotation L (rotation L P)))) := by
      simp only [map_neg, neg_neg, map_nsmul, rotation_cube_apply]
    _ = -rotation L (rotation L (Affine.Point.some (doubleX x) (minusDoubleY x y) hD)) :=
      congrArg (fun Q : Points L => -rotation L (rotation L Q)) eD
    _ = _ := by
      rw [eR, eR', Affine.Point.neg_some, Affine.Point.some.injEq]
      exact ⟨eX, eY⟩

set_option maxHeartbeats 1000000 in
private theorem regular_comparison {x y : L} (hP : (Curve (1 : L)).Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) (hg : x ^ 3 + 4 ≠ 0) :
    (3 : ℕ) • (Affine.Point.some x y hP : Points L) = (2 : ℕ) • rotation L (Affine.Point.some x y hP) ↔
      torsionCubic (x ^ 3) = 0 := by
  have h₂ : (2 : L) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : L) ≠ 0 := numeral_ne_zero 3 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero L) x y).mp hP
  have hs : x ^ 3 + 1 ≠ 0 := he ▸ pow_ne_zero 2 hy
  obtain ⟨hT, eT⟩ := triple_some_coordinates h₂ h₃ (discriminant_ne_zero L)
    hy hx (by simpa only [mul_one] using hg) (tripleX_correct hx hg) hP
  have hY := tripleY_correct hx hy hg he
  have hT' : (Curve (1 : L)).Nonsingular (tripleX x) (tripleY x y) := by
    simpa only [hY] using hT
  have hTriple : (3 : ℕ) • (Affine.Point.some x y hP : Points L) =
      Affine.Point.some (tripleX x) (tripleY x y) hT' := by
    refine eT.trans ?_
    rw [Affine.Point.some.injEq]
    exact ⟨rfl, hY⟩
  obtain ⟨hD, eD⟩ := rotated_double_some L hP hy
  rw [hTriple, eD, Affine.Point.some.injEq, ← fractional_coordinates_iff (x ^ 3) (pow_ne_zero _ hx) hs hg]
  unfold tripleX tripleY singleDoubleX positiveDoubleY
  constructor
  · rintro ⟨hX, hY'⟩
    exact ⟨mul_left_cancel₀ hx hX, mul_left_cancel₀ hy hY'⟩
  · rintro ⟨hX, hY'⟩
    exact ⟨congrArg (fun z : L => x * z) hX, congrArg (fun z : L => y * z) hY'⟩

set_option maxHeartbeats 800000 in
theorem torsion_some_iff {x y : L} (hP : (Curve (1 : L)).Nonsingular x y) :
    (19 : ℕ) • (Affine.Point.some x y hP : Points L) = 0 ↔ torsionCubic (x ^ 3) = 0 := by
  let P : Points L := .some x y hP
  have h₂ : (2 : L) ≠ 0 := numeral_ne_zero 2 (by decide)
  have h₃ : (3 : L) ≠ 0 := numeral_ne_zero 3 (by decide)
  have he := (nonsingular_iff (discriminant_ne_zero L) x y).mp hP
  obtain ⟨hR, eR⟩ := rotation_some L hP
  have hTwoRot : (2 : ℕ) • rotation L P = 0 ↔ y = 0 := by
    change (2 : ℕ) • rotation L (Affine.Point.some x y hP) = 0 ↔ y = 0
    rw [eR]
    exact two_nsmul_affine_some_iff h₂ hR
  change (19 : ℕ) • P = 0 ↔ _
  rw [torsion_iff L P]
  constructor
  · intro hEq
    have hy : y ≠ 0 := by
      intro hy
      have hTwo : (2 : ℕ) • P = 0 := (two_nsmul_affine_some_iff h₂ hP).mpr hy
      have hThree : (3 : ℕ) • P = P := by
        rw [show (3 : ℕ) = 2 + 1 by decide, add_nsmul, one_nsmul, hTwo, zero_add]
      exact Affine.Point.some_ne_zero hP (hThree.symm.trans (hEq.trans (hTwoRot.mpr hy)))
    have hNonzero : (3 : ℕ) • P ≠ 0 := fun h => hy (hTwoRot.mp (hEq.symm.trans h))
    have hx : x ≠ 0 := by
      intro hz
      apply hNonzero
      apply (three_nsmul_affine_some_iff h₂ h₃ (discriminant_ne_zero L) hP).mpr
      exact ⟨hy, by simp [hz]⟩
    have hg : x ^ 3 + 4 ≠ 0 := by
      intro hz
      apply hNonzero
      apply (three_nsmul_affine_some_iff h₂ h₃ (discriminant_ne_zero L) hP).mpr
      exact ⟨hy, by rw [mul_one, hz, mul_zero]⟩
    exact (regular_comparison L hP hx hy hg).mp hEq
  · intro hRoot
    obtain ⟨ht, hs, hg⟩ := torsionCubic_nonzero_values hRoot
    have hx : x ≠ 0 := fun h => ht (by simp [h])
    have hy : y ≠ 0 := fun h => hs (by simpa [h] using he.symm)
    exact (regular_comparison L hP hx hy hg).mpr hRoot

end
end ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinates

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinates.torsion_some_iff
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
