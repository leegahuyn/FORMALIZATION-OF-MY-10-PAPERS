import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicGenericFunctionField
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace

/-! The centered cubic's generic point and the subgroup with rational abscissas. -/

namespace ManuscriptAudit.CubicGenericAntiInvariant

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitFrobeniusTrace CubicGenericFunctionField CubicTwoTorsion

noncomputable section
open scoped Classical

variable {K : Type*} [Field K] (A : K)

/-- The actual point group over the quadratic function field of the centered cubic. -/
abbrev Points := (Curve (algebraMap K (Model A) A)).Point

/-- The sign change of the generic ordinate acts on the actual point group. -/
def sigma : Points A →+ Points A :=
  pointMapAt K (Model A) (Curve A) (Curve (algebraMap K (Model A) A))
    (centered_baseChange K (Model A) A) ((conjugation A).restrictScalars K)

/-- Points for which the function field involution acts as elliptic negation. -/
def antiInvariant : AddSubgroup (Points A) where
  carrier := {P | sigma A P = -P}
  zero_mem' := by simp
  add_mem' := by
    intro P Q hP hQ
    change sigma A P = -P at hP
    change sigma A Q = -Q at hQ
    change sigma A (P + Q) = -(P + Q)
    rw [map_add, hP, hQ, neg_add]
  neg_mem' := by
    intro P hP
    change sigma A P = -P at hP
    change sigma A (-P) = -(-P)
    rw [map_neg, hP]

/-- The abscissa of an anti-invariant finite point is literally a rational function in X. -/
theorem abscissa_fixed {x y : Model A} {hP : (Curve (algebraMap K (Model A) A)).Nonsingular x y}
    (h : (Affine.Point.some x y hP : Points A) ∈ antiInvariant A) :
    conjugation A x = x := by
  change sigma A (.some x y hP) = -(.some x y hP : Points A) at h
  obtain ⟨h', he⟩ := pointMapAt_some K (Model A) (Curve A) (Curve (algebraMap K (Model A) A))
    (centered_baseChange K (Model A) A) ((conjugation A).restrictScalars K) x y hP
  change sigma A (.some x y hP) = .some (conjugation A x) (conjugation A y) h' at he
  rw [he, Affine.Point.neg_some, Affine.Point.some.injEq] at h
  exact h.1

/-- The actual generic point of the centered cubic. -/
def genericPoint (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) : Points A := by
  have h₂' : (2 : Model A) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₂
  have h₃' : (3 : Model A) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K (Model A))).mpr h₃
  have hA' := (map_ne_zero (algebraMap K (Model A))).mpr hA
  have hΔ := CubicThreeTorsionCard.shortCubic_discriminant_ne_zero h₂' h₃' hA'
  exact .some (genericX A) (genericY A)
    ((nonsingular_iff hΔ _ _).mpr (generic_equation A))

theorem genericPoint_mem_antiInvariant (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    genericPoint A h₂ h₃ hA ∈ antiInvariant A := by
  let P := genericPoint A h₂ h₃ hA
  change sigma A P = -P
  have hP : ∃ h, P = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
  obtain ⟨h, he⟩ := hP
  obtain ⟨h', he'⟩ := pointMapAt_some K (Model A) (Curve A) (Curve (algebraMap K (Model A) A))
    (centered_baseChange K (Model A) A) ((conjugation A).restrictScalars K)
    (genericX A) (genericY A) h
  change sigma A (.some (genericX A) (genericY A) h) =
    .some (conjugation A (genericX A)) (conjugation A (genericY A)) h' at he'
  rw [he, he', Affine.Point.neg_some, Affine.Point.some.injEq, conjugation_genericY]
  constructor
  · exact (conjugation A).commutes _
  · simp [Curve, CubicAffine, shortCubic, Affine.negY]

end

end ManuscriptAudit.CubicGenericAntiInvariant

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicGenericAntiInvariant.abscissa_fixed,
      ``ManuscriptAudit.CubicGenericAntiInvariant.genericPoint_mem_antiInvariant] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
