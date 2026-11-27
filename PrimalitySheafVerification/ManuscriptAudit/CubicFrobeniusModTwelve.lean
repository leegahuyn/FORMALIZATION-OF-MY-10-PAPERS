import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.TwelveTorsionCRTTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusModFourArithmetic
import PrimalitySheafVerification.ManuscriptAudit.CubicThreeFrobeniusCharpoly

/-! Exact arithmetic Frobenius coefficients on actual twelve-torsion of the good centered cubic. -/

namespace ManuscriptAudit.CubicFrobeniusModTwelve

open Polynomial Module CubicThreeTorsionOrdinate
open CubicNonsplitThreeAdicTrace CubicNonsplitFrobeniusTrace TorsionFrobeniusModule
open CubicSplitExtensionTraceRecurrence TwelveTorsionCRTBasis TwelveTorsionCRTTrace
open Paper5PrintedRecurrence

noncomputable section

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]

private def basisFour {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) (ZMod 4) (Torsion 4 (GeometricPoints K L A)) := by
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  exact CubicTwoPowerTorsionBasis.affineBasis h₂L h₃L
    ((map_ne_zero (algebraMap K L)).mpr hA) 2

private def basisThree {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) (ZMod 3) (Torsion 3 (GeometricPoints K L A)) :=
  (CubicThreeFrobeniusActual.actualTorsionBasis K L h₂ h₃ hA).map
    (torsionTransport L 3 (centered_baseChange K L A))

private theorem trace_det_three {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) :
    let F := mapLinear 3 (arithmeticPointFrobenius K L A)
    LinearMap.trace (ZMod 3) (Torsion 3 (GeometricPoints K L A)) F = (signedTrace A : ZMod 3) ∧
      LinearMap.det F = (Fintype.card K : ZMod 3) := by
  let W := Curve A
  let V := Curve (algebraMap K L A)
  let h := centered_baseChange K L A
  let e := torsionTransport L 3 h
  let g := FiniteField.frobeniusAlgHom K L
  let F := CubicThreeFrobeniusActual.actualFrobenius K L A
  have he : e.conj F = mapLinear 3 (arithmeticPointFrobenius K L A) :=
    mapLinear_transport K L W V h g 3
  obtain ⟨ht, hd⟩ := CubicThreeFrobeniusCharpoly.actualFrobenius_arithmetic_trace_det K L h₂ h₃ hA
  dsimp only
  rw [← he]
  refine ⟨(LinearMap.trace_conj' F e).trans ht, ?_⟩
  have hMap : e.conj F = e.toLinearMap ∘ₗ F ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro P
    rfl
  rw [hMap]
  exact (LinearMap.det_conj F e).trans hd

def basisTwelve {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    Basis (Fin 2) (ZMod 12) (Torsion 12 (GeometricPoints K L A)) :=
  basis (GeometricPoints K L A) (basisFour K L h₂ h₃ hA) (basisThree K L h₂ h₃ hA)

abbrev native (A : K) : Module.End (ZMod 12) (Torsion 12 (GeometricPoints K L A)) :=
  mapLinear 12 (arithmeticPointFrobenius K L A)

/-- On actual geometric twelve-torsion the trace and determinant are the signed projective
point count and finite-field cardinality, respectively. -/
theorem trace_det {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    LinearMap.trace (ZMod 12) (Torsion 12 (GeometricPoints K L A)) (native K L A) =
      (signedTrace A : ZMod 12) ∧
    LinearMap.det (native K L A) = (Fintype.card K : ZMod 12) := by
  let G := GeometricPoints K L A
  let f := arithmeticPointFrobenius K L A
  let B₄ := basisFour K L h₂ h₃ hA
  let B₃ := basisThree K L h₂ h₃ hA
  have h4 := trace_det_reduce_four G B₄ B₃ f
  have h3 := trace_det_reduce_three G B₄ B₃ f
  obtain ⟨ht3, hd3⟩ := trace_det_three K L h₂ h₃ hA
  have ht4 := CubicFrobeniusModFourArithmetic.trace_eq_signed_count K L h₂ h₃ hA
  have hd4 := CubicFrobeniusDeterminantModFour.determinant_eq_card K L h₂ h₃ hA
  constructor
  · apply reduce_injective
    · rw [map_intCast]
      exact h4.1.trans ht4
    · rw [map_intCast]
      exact h3.1.trans ht3
  · apply reduce_injective
    · rw [map_natCast]
      exact h4.2.trans hd4
    · rw [map_natCast]
      exact h3.2.trans hd3

/-- The actual rank-two characteristic polynomial on twelve-torsion. -/
theorem charpoly_eq_signed_count {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    let B := basisTwelve K L h₂ h₃ hA
    letI : Module.Free (ZMod 12) (Torsion 12 (GeometricPoints K L A)) := Module.Free.of_basis B
    letI : Module.Finite (ZMod 12) (Torsion 12 (GeometricPoints K L A)) := Module.Finite.of_basis B
    (native K L A).charpoly =
      X ^ 2 - C (signedTrace A : ZMod 12) * X + C (Fintype.card K : ZMod 12) := by
  letI : Fact (1 < (12 : ℕ)) := ⟨by decide⟩
  let B := basisTwelve K L h₂ h₃ hA
  letI : Module.Free (ZMod 12) (Torsion 12 (GeometricPoints K L A)) := Module.Free.of_basis B
  letI : Module.Finite (ZMod 12) (Torsion 12 (GeometricPoints K L A)) := Module.Finite.of_basis B
  obtain ⟨ht, hd⟩ := trace_det K L h₂ h₃ hA
  dsimp only
  rw [← LinearMap.charpoly_toMatrix _ B, Matrix.charpoly_fin_two,
    ← LinearMap.trace_eq_matrix_trace (ZMod 12) B, LinearMap.det_toMatrix B, ht, hd]

/-- The arithmetic recurrence determines every power trace on native twelve-torsion. -/
theorem trace_power_eq_recurrence {A : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (n : ℕ) :
    LinearMap.trace (ZMod 12) (Torsion 12 (GeometricPoints K L A)) (native K L A ^ n) =
      (recurrence (Fintype.card K) (signedTrace A) n : ZMod 12) := by
  letI : Fact (1 < (12 : ℕ)) := ⟨by decide⟩
  obtain ⟨ht, hd⟩ := trace_det K L h₂ h₃ hA
  exact Paper5LinearTraceRecurrence.trace_pow_eq_recurrence (basisTwelve K L h₂ h₃ hA)
    (native K L A) (Fintype.card K) (signedTrace A) ht hd n

end
end ManuscriptAudit.CubicFrobeniusModTwelve

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicFrobeniusModTwelve.trace_det,
      ``ManuscriptAudit.CubicFrobeniusModTwelve.charpoly_eq_signed_count,
      ``ManuscriptAudit.CubicFrobeniusModTwelve.trace_power_eq_recurrence] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
