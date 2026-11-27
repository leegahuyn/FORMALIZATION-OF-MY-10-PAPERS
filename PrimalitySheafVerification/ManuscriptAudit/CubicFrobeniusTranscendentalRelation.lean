import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericCharacteristicRelation
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericSpecialization
import PrimalitySheafVerification.ManuscriptAudit.CubicNativePointBaseChange

/-! The relative Frobenius relation specializes to the actual points with transcendental abscissa. -/

namespace ManuscriptAudit.CubicFrobeniusTranscendentalRelation

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant CubicGenericSecantHeight
open CubicGenericFrobeniusHeight CubicGenericCharacteristicRelation CubicGenericSpecialization
open CubicNativePointBaseChange

noncomputable section
open scoped Classical

variable (K L : Type*) [Field K] [Fintype K] [Field L] [DecidableEq L] [Algebra K L]

/-- The integer dictated by the actual projective point count. -/
def arithmeticTrace (A : K) : ℤ :=
  (Fintype.card K : ℤ) + 1 - Nat.card (shortCubic (0 : K) A).toProjective.Point

/-- The candidate arithmetic characteristic polynomial evaluated on actual relative Frobenius. -/
def characteristicError (A : K) : AddMonoid.End (GeometricPoints K L A) :=
  let F := arithmeticPointFrobenius K L A
  F ^ 2 - arithmeticTrace K A • F + (Fintype.card K : ℤ) • 1

theorem characteristicError_apply (A : K) (P : GeometricPoints K L A) :
    let F := arithmeticPointFrobenius K L A
    characteristicError K L A P =
      F (F P) - arithmeticTrace K A • F P + (Fintype.card K : ℤ) • P := by
  simp only [characteristicError, pow_two, AddMonoidHom.add_apply, AddMonoidHom.sub_apply,
    AddMonoidHom.zsmul_apply, AddMonoid.End.one_apply] <;> rfl

/-- On a point with transcendental abscissa, the actual characteristic error is two-torsion. -/
theorem characteristicError_transcendental {k : ℕ} (hq : Fintype.card K = 2 * k + 1) (hk : 0 < k)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hchar : ringChar K ≠ 2)
    {A : K} (hA : A ≠ 0) {x y : L}
    (hP : (Curve (algebraMap K L A)).Nonsingular x y)
    (hx : Transcendental K x) :
    (2 : ℕ) • characteristicError K L A (.some x y hP) = 0 := by
  let G := Model A
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂' h₃'
    ((map_ne_zero (algebraMap K L)).mpr hA)
  have hy := (nonsingular_iff hΔ x y).mp hP
  obtain ⟨g, hX, hY⟩ := exists_specialization A x y hx hy
  let Q := genericPoint A h₂ h₃ hA
  have hQ : ∃ h, Q = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
  obtain ⟨h, he⟩ := hQ
  obtain ⟨hI, hMap⟩ := pointsMap_some A g (genericX A) (genericY A) h
  have hCoord : (Affine.Point.some (g (genericX A)) (g (genericY A)) hI :
      GeometricPoints K L A) = .some x y hP := by
    rw [Affine.Point.some.injEq]
    exact ⟨hX, hY⟩
  have hQMap : pointsMap A g Q = .some x y hP := by rw [he, hMap, hCoord]
  have hRel := generic_relation_two_nsmul A hq hk h₂ h₃ hchar hA
  have hRel' := congrArg (fun P : antiInvariant A => P.val) hRel
  let F := arithmeticPointFrobenius K G A
  change (2 : ℕ) • (F (F Q) - arithmeticTrace K A • F Q + (Fintype.card K : ℤ) • Q) = 0 at hRel'
  have hComm (P : GeometricPoints K G A) : pointsMap A g (F P) =
      arithmeticPointFrobenius K L A (pointsMap A g P) :=
    map_arithmeticFrobenius (K := K) (L := G) (M := L) A g P
  have hImage := congrArg (pointsMap A g) hRel'
  rw [characteristicError_apply]
  simpa only [map_nsmul, map_add, map_sub, map_zsmul, map_zero, hComm, hQMap] using hImage

end

end ManuscriptAudit.CubicFrobeniusTranscendentalRelation

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicFrobeniusTranscendentalRelation.characteristicError_apply,
      ``ManuscriptAudit.CubicFrobeniusTranscendentalRelation.characteristicError_transcendental] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
