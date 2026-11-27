import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalPointEnd
import PrimalitySheafVerification.ManuscriptAudit.RationalMapFiberBound

/-! A field-natural point operation can be compared with its literal generic rational abscissa. -/

namespace ManuscriptAudit.CubicNaturalRationalEval

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicGenericFunctionField CubicGenericAntiInvariant
open CubicGenericSpecialization CubicNativePointBaseChange CubicNaturalPointEnd
open RationalMapFiberBound

noncomputable section
open scoped Classical

universe u

variable {K M : Type u} [Field K] [Field M] [DecidableEq M] [Algebra K M] {A : K}

/-- An actual transcendental input and its actual image obey the same fiber equation
as the generic point, by injective field specialization. -/
theorem isRoot_of_image (D : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) (r : RatFunc K)
    {s : Model A}
    {hQ : (Curve (algebraMap K (Model A) A)).Nonsingular (algebraMap (RatFunc K) (Model A) r) s}
    (he : D.atField (Model A) (genericPoint A h₂ h₃ hA) =
      .some (algebraMap (RatFunc K) (Model A) r) s hQ)
    (hΔ : (shortCubic (0 : M) (algebraMap K M A)).Δ ≠ 0)
    {x y t v : M} (hxy : (Curve (algebraMap K M A)).Nonsingular x y)
    (htv : (Curve (algebraMap K M A)).Nonsingular t v) (hx : Transcendental K x)
    (hImage : D.atField M (.some x y hxy) = .some t v htv) :
    (fiberPolynomial r t).IsRoot x := by
  let Q := genericPoint A h₂ h₃ hA
  have hy := (nonsingular_iff hΔ x y).mp hxy
  obtain ⟨g, hX, hY⟩ := exists_specialization A x y hx hy
  obtain ⟨hQ', hEq⟩ : ∃ h, Q = .some (genericX A) (genericY A) h := ⟨_, rfl⟩
  obtain ⟨hI, hMap⟩ := pointsMap_some A g (genericX A) (genericY A) hQ'
  have hCoord : (Affine.Point.some (g (genericX A)) (g (genericY A)) hI :
      GeometricPoints K M A) = .some x y hxy := by
    rw [Affine.Point.some.injEq]
    exact ⟨hX, hY⟩
  have hQMap : pointsMap A g Q = .some x y hxy := by rw [hEq, hMap, hCoord]
  have hD := D.commute g Q
  rw [hQMap, hImage, show D.atField (Model A) Q = _ from he] at hD
  obtain ⟨hI', hMap'⟩ := pointsMap_some A g (algebraMap (RatFunc K) (Model A) r) s hQ
  rw [hMap', Affine.Point.some.injEq] at hD
  have hR := isRoot_of_specialization A g r
  rw [hD.1, hX] at hR
  exact hR

end

end ManuscriptAudit.CubicNaturalRationalEval

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicNaturalRationalEval.isRoot_of_image
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
