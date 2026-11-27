import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNativePointBaseChange
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericAntiInvariant
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericSpecialization

/-! Additive point operations that commute with field extension on the literal centered model. -/

namespace ManuscriptAudit.CubicNaturalPointEnd

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicNonsplitThreeAdicTrace CubicNativePointBaseChange
open CubicGenericFunctionField CubicGenericAntiInvariant

noncomputable section
open scoped Classical

universe u

/-- A family of additive endomorphisms, natural in every field extension of the same universe. -/
structure Family (K : Type u) [Field K] (A : K) where
  atField : (L : Type u) → [Field L] → [DecidableEq L] → [Algebra K L] →
    AddMonoid.End (GeometricPoints K L A)
  commute : ∀ {L M : Type u} [Field L] [DecidableEq L] [Algebra K L]
    [Field M] [DecidableEq M] [Algebra K M]
    (g : L →ₐ[K] M) (P : GeometricPoints K L A),
    pointsMap A g (atField L P) = atField M (pointsMap A g P)

variable {K : Type u} [Field K] {A : K}

private theorem pointsMap_conjugation (P : Points A) :
    pointsMap A ((conjugation A).restrictScalars K) P = sigma A P := by
  let g := (conjugation A).restrictScalars K
  cases P with
  | zero =>
    change pointsMap A g (0 : Points A) = sigma A 0
    rw [map_zero, map_zero]
  | some x y h =>
    obtain ⟨h₁, e₁⟩ := pointsMap_some A g x y h
    obtain ⟨h₂, e₂⟩ := pointMapAt_some K (Model A) (Curve A)
      (Curve (algebraMap K (Model A) A)) (centered_baseChange K (Model A) A) g x y h
    change pointsMap A g (.some x y h) = pointMapAt K (Model A) (Curve A)
      (Curve (algebraMap K (Model A) A)) (centered_baseChange K (Model A) A) g (.some x y h)
    rw [e₁, e₂]

/-- Naturality makes the sign anti-invariant subgroup stable under any such operation. -/
def antiInvariantApply (D : Family K A) (P : antiInvariant A) : antiInvariant A := by
  refine ⟨D.atField (Model A) P.val, ?_⟩
  change sigma A (D.atField (Model A) P.val) = -(D.atField (Model A) P.val)
  have hP : sigma A P.val = -P.val := P.property
  rw [← pointsMap_conjugation, D.commute, pointsMap_conjugation, hP, map_neg]

/-- Doubling the output retains the same field naturality. -/
def double (D : Family K A) : Family K A where
  atField L := 2 • D.atField L
  commute g P := by
    simp only [AddMonoidHom.nsmul_apply, map_nsmul, D.commute]

/-- Every field-natural additive operation is detected on the generic affine solution
when tested at a point of transcendental abscissa. -/
theorem eval_transcendental {L : Type u} [Field L] [DecidableEq L] [Algebra K L]
    (D : Family K A) (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    {x y : L} (hP : (Curve (algebraMap K L A)).Nonsingular x y)
    (hx : Transcendental K x) :
    D.atField L (.some x y hP) = 0 ↔ D.atField (Model A) (genericPoint A h₂ h₃ hA) = 0 := by
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂' h₃'
    ((map_ne_zero (algebraMap K L)).mpr hA)
  have hy := (nonsingular_iff hΔ x y).mp hP
  obtain ⟨g, hX, hY⟩ := CubicGenericSpecialization.exists_specialization A x y hx hy
  let Q := genericPoint A h₂ h₃ hA
  obtain ⟨hQ, he⟩ : ∃ h, Q = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
  obtain ⟨hI, hMap⟩ := pointsMap_some A g (genericX A) (genericY A) hQ
  have hCoord : (Affine.Point.some (g (genericX A)) (g (genericY A)) hI :
      GeometricPoints K L A) = .some x y hP := by
    rw [Affine.Point.some.injEq]
    exact ⟨hX, hY⟩
  have hQMap : pointsMap A g Q = .some x y hP := by rw [he, hMap, hCoord]
  have hD := D.commute g Q
  rw [hQMap, ← hD, ← map_zero (pointsMap A g)]
  exact (pointsMap_injective A g).eq_iff

end

end ManuscriptAudit.CubicNaturalPointEnd

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicNaturalPointEnd.antiInvariantApply,
      ``ManuscriptAudit.CubicNaturalPointEnd.double,
      ``ManuscriptAudit.CubicNaturalPointEnd.eval_transcendental] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
