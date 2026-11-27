import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.CubicNaturalPointEnd
import PrimalitySheafVerification.ManuscriptAudit.CubicAlgebraicAbscissaDescent
import PrimalitySheafVerification.ManuscriptAudit.CubicDoublingSurjective

/-! Faithfulness of generic evaluation for additive point operations natural in field extensions. -/

namespace ManuscriptAudit.CubicNaturalPointEnd

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace
open CubicGenericFunctionField CubicGenericAntiInvariant
open CubicNativePointBaseChange CubicAlgebraicAbscissaDescent

noncomputable section
open scoped Classical

universe u

variable {K L : Type u} [Field K] [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]
  {A : K}

/-- A field-natural additive endomorphism that kills the generic point kills all geometric points. -/
theorem eq_zero_of_generic (D : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hGeneric : D.atField (Model A) (genericPoint A h₂ h₃ hA) = 0) : D.atField L = 0 := by
  apply AddMonoidHom.ext
  intro P
  change D.atField L P = 0
  let a := algebraMap K L A
  let M := Model a
  letI : Algebra K (RatFunc L) := inferInstance
  letI : IsScalarTower K L (RatFunc L) := inferInstance
  letI : Algebra K M := inferInstanceAs (Algebra K (QuadraticAlgebra (RatFunc L) (radicand a) 0))
  letI : IsScalarTower K L M :=
    inferInstanceAs (IsScalarTower K L (QuadraticAlgebra (RatFunc L) (radicand a) 0))
  let f := IsScalarTower.toAlgHom K L M
  let b := pointsMap A f
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hA' : a ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  let Q : GeometricPoints K M A := genericPoint a h₂' h₃' hA'
  have hQ : ∃ h, Q = .some (genericX a) (genericY a) h := ⟨_, rfl⟩
  have hTrans : Transcendental L (genericX a) :=
    (transcendental_algebraMap_iff (algebraMap (RatFunc L) M).injective).mpr RatFunc.transcendental_X
  have hOutside : Q ∉ Set.range b := by
    rintro ⟨R, hR⟩
    obtain ⟨hP, he⟩ := hQ
    cases R with
    | zero =>
      have hZ : (0 : GeometricPoints K M A) = Q := (map_zero b).symm.trans hR
      rw [he] at hZ
      cases hZ
    | some x y hxy =>
      obtain ⟨h', hMap⟩ := pointsMap_some A f x y hxy
      change pointsMap A f (.some x y hxy) = Q at hR
      rw [hMap, he, Affine.Point.some.injEq] at hR
      have hx : algebraMap L M x = genericX a := hR.1
      exact hTrans (hx ▸ isAlgebraic_algebraMap (A := M) x)
  have hOutsideSum : b P + Q ∉ Set.range b := by
    rintro ⟨R, he⟩
    apply hOutside
    refine ⟨R - P, ?_⟩
    rw [map_sub, he]
    abel
  have hOutsideError (R : GeometricPoints K M A) (hR : R ∉ Set.range b) :
      D.atField M R = 0 := by
    cases R with
    | zero =>
      change (0 : GeometricPoints K M A) ∉ Set.range b at hR
      exact (hR ⟨0, map_zero b⟩).elim
    | some x y hxy =>
      have hx : Transcendental L x := fun hAlg => hR
        (in_range_of_isAlgebraic A h₂ h₃ hA hxy hAlg)
      exact (eval_transcendental D h₂ h₃ hA hxy (Transcendental.of_tower_top K hx)).mpr hGeneric
  have hQError := hOutsideError Q hOutside
  have hSumError := hOutsideError (b P + Q) hOutsideSum
  have hErrImage : D.atField M (b P) = 0 := by
    simpa only [map_add, hQError, add_zero] using hSumError
  apply (pointsMap_injective A f)
  rw [D.commute, map_zero]
  exact hErrImage


/-- Even a two-torsion output at the generic point forces the operation to vanish. -/
theorem eq_zero_of_two_torsion_generic (D : Family K A)
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hGeneric : (2 : ℕ) • D.atField (Model A) (genericPoint A h₂ h₃ hA) = 0) :
    D.atField L = 0 := by
  have hD : (double D).atField L = 0 := eq_zero_of_generic (double D) h₂ h₃ hA
    (by
      change (2 : ℕ) • D.atField (Model A) (genericPoint A h₂ h₃ hA) = 0
      exact hGeneric)
  have h₂' : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃' : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hA' := (map_ne_zero (algebraMap K L)).mpr hA
  apply AddMonoidHom.ext
  intro P
  obtain ⟨R, hR⟩ := CubicDoublingSurjective.affine_doubling_surjective h₂' h₃' hA' P
  change D.atField L P = 0
  rw [← hR, map_nsmul]
  exact congrArg (fun f : AddMonoid.End (GeometricPoints K L A) => f R) hD

end

end ManuscriptAudit.CubicNaturalPointEnd

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicNaturalPointEnd.eq_zero_of_generic,
      ``ManuscriptAudit.CubicNaturalPointEnd.eq_zero_of_two_torsion_generic] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
