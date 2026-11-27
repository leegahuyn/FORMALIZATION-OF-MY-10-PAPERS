import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalPointEnd
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationQuadratic
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusRotationMap
import PrimalitySheafVerification.ManuscriptAudit.RotationNormUnit

/-! Base-defined cube rotation and Frobenius minus an integral combination on actual curves. -/

namespace ManuscriptAudit.CubicNaturalCMOperations

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicNonsplitThreeAdicTrace CubicNativePointBaseChange
open CubicCubeRotation CubicRotationQuadratic CubicFrobeniusRotationMap
open CubicNaturalPointEnd RotationNormUnit

noncomputable section
open scoped Classical

universe u

variable {K : Type u} [Field K] {A z : K}
variable (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (hz : z ^ 3 = 1)

private theorem image_two (L : Type u) [Field L] [Algebra K L] : (2 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂

private theorem image_three (L : Type u) [Field L] [Algebra K L] : (3 : L) ≠ 0 := by
  simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃

private theorem image_A (L : Type u) [Field L] [Algebra K L] : algebraMap K L A ≠ 0 :=
  (map_ne_zero (algebraMap K L)).mpr hA

private theorem image_cube (L : Type u) [Field L] [Algebra K L] :
    (algebraMap K L z) ^ 3 = 1 := by rw [← map_pow, hz, map_one]

private theorem image_disc (L : Type u) [Field L] [Algebra K L] :
    (shortCubic (0 : L) (algebraMap K L A)).Δ ≠ 0 :=
  CubicThreeTorsionCard.shortCubic_discriminant_ne_zero (image_two h₂ L) (image_three h₃ L)
    (image_A hA L)

/-- The cube rotation defined over the base is natural over all extensions. -/
def rotation : Family K A where
  atField L := rotate (algebraMap K L z) (image_cube hz L) (image_disc h₂ h₃ hA L)
  commute := by
    intro L M _ _ _ _ _ _ g P
    let rL := rotate (algebraMap K L z) (image_cube hz L) (image_disc h₂ h₃ hA L)
    let rM := rotate (algebraMap K M z) (image_cube hz M) (image_disc h₂ h₃ hA M)
    change pointsMap A g (rL P) = rM (pointsMap A g P)
    cases P with
    | zero =>
      change pointsMap A g (rL 0) = rM (pointsMap A g 0)
      simp only [map_zero]
    | some x y h =>
      have hr : ∃ h', rL (Affine.Point.some x y h) = .some (algebraMap K L z * x) y h' :=
        ⟨_, rotate_some (image_cube hz L) (image_disc h₂ h₃ hA L) h⟩
      obtain ⟨h', e'⟩ := hr
      obtain ⟨h₁, e₁⟩ := pointsMap_some A g (algebraMap K L z * x) y h'
      obtain ⟨h₂', e₂⟩ := pointsMap_some A g x y h
      rw [e', e₁, e₂]
      dsimp only [rM]
      rw [rotate_some, Affine.Point.some.injEq]
      exact ⟨by rw [map_mul, g.commutes], rfl⟩

variable (L : Type u) [Field L] [DecidableEq L] [Algebra K L]

/-- This native endomorphism satisfies the primitive cubic quadratic. -/
theorem rotation_quadratic (hz₁ : z ≠ 1) :
    let r := (rotation h₂ h₃ hA hz).atField L
    r ^ 2 + r + 1 = 0 := by
  let r := (rotation h₂ h₃ hA hz).atField L
  have hz₁' : algebraMap K L z ≠ 1 := by
    intro he
    apply hz₁
    apply (algebraMap K L).injective
    rw [map_one, he]
  apply AddMonoidHom.ext
  intro P
  change r (r P) + r P + P = 0
  exact rotate_sum_eq_zero (image_two h₂ L) (image_three h₃ L) (image_A hA L)
    (image_cube hz L) hz₁' (image_disc h₂ h₃ hA L) P

variable [Fintype K]

/-- Relative Frobenius commutes with a base-defined native cube rotation. -/
theorem commutes_frobenius :
    Commute (arithmeticPointFrobenius K L A) ((rotation h₂ h₃ hA hz).atField L) := by
  let g := FiniteField.frobeniusAlgHom K L
  apply AddMonoidHom.ext
  intro P
  change arithmeticPointFrobenius K L A ((rotation h₂ h₃ hA hz).atField L P) =
    (rotation h₂ h₃ hA hz).atField L (arithmeticPointFrobenius K L A P)
  exact pointMapAt_intertwines_rotation K L (Curve A) (centered_baseChange K L A) g
    (g.commutes z) (image_cube hz L) (image_cube hz L) (image_disc h₂ h₃ hA L) P

/-- Frobenius minus an integral linear combination is natural over field embeddings. -/
def difference (a b : ℤ) : Family K A where
  atField L := arithmeticPointFrobenius K L A -
    combination ((rotation h₂ h₃ hA hz).atField L) a b
  commute := by
    intro L M _ _ _ _ _ _ g P
    let R := rotation h₂ h₃ hA hz
    have hR := R.commute g P
    simp only [combination, AddMonoidHom.sub_apply, AddMonoidHom.add_apply,
      AddMonoidHom.zsmul_apply, AddMonoid.End.one_apply, map_sub, map_add,
      map_zsmul, map_arithmeticFrobenius]
    rw [hR]

end

end ManuscriptAudit.CubicNaturalCMOperations

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicNaturalCMOperations.rotation,
      ``ManuscriptAudit.CubicNaturalCMOperations.rotation_quadratic,
      ``ManuscriptAudit.CubicNaturalCMOperations.commutes_frobenius,
      ``ManuscriptAudit.CubicNaturalCMOperations.difference] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
