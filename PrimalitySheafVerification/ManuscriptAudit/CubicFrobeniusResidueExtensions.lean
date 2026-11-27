import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusModTwelve
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt

/-! Frobenius powers on the actual twelve-torsion recover extension point counts modulo twelve. -/

namespace ManuscriptAudit.CubicFrobeniusResidueExtensions

open CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace TorsionFrobeniusModule
open CubicSplitExtensionTraceRecurrence CubicExtensionFrobeniusAt

noncomputable section

variable (K E L : Type*) [Field K] [Field E] [Field L]
  [Fintype K] [Fintype E] [DecidableEq E] [DecidableEq L] [IsAlgClosed L]
  [Algebra K E] [Algebra E L] [Algebra K L] [IsScalarTower K E L]

private theorem trace_det_at (m : ℕ) (a : E) (v : L) (h : algebraMap E L a = v) :
    LinearMap.trace (ZMod m) (Torsion m (Curve v).Point) (scalarActionAt E L m a v h) =
      LinearMap.trace (ZMod m) (Torsion m (GeometricPoints E L a))
        (mapLinear m (arithmeticPointFrobenius E L a)) ∧
    LinearMap.det (scalarActionAt E L m a v h) =
      LinearMap.det (mapLinear m (arithmeticPointFrobenius E L a)) := by
  subst v
  exact ⟨rfl, rfl⟩

private theorem coefficients_at_extension (m : ℕ) (A : K) (n : ℕ)
    (hCard : Fintype.card E = Fintype.card K ^ n) :
    let a := algebraMap K E A
    let F := mapLinear m (arithmeticPointFrobenius K L A)
    LinearMap.trace (ZMod m) (Torsion m (GeometricPoints K L A)) (F ^ n) =
      LinearMap.trace (ZMod m) (Torsion m (GeometricPoints E L a))
        (mapLinear m (arithmeticPointFrobenius E L a)) ∧
    LinearMap.det (F ^ n) = LinearMap.det (mapLinear m (arithmeticPointFrobenius E L a)) := by
  have hA : algebraMap E L (algebraMap K E A) = algebraMap K L A :=
    (IsScalarTower.algebraMap_apply K E L A).symm
  have h := trace_det_at E L m (algebraMap K E A) (algebraMap K L A) hA
  rw [CubicExtensionFrobeniusAt.eq_pow K E L m n A hA hCard] at h
  exact h

/-- Both characteristic coefficients of the actual extension power agree with
the signed projective point count and field size modulo twelve. -/
theorem trace_det_power_eq_extension_count {A : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0) :
    let F := CubicFrobeniusModTwelve.native K L A
    let n := Module.finrank K E
    LinearMap.trace (ZMod 12) (Torsion 12 (GeometricPoints K L A)) (F ^ n) =
      (signedTrace (algebraMap K E A) : ZMod 12) ∧
    LinearMap.det (F ^ n) = (Fintype.card E : ZMod 12) := by
  let i := algebraMap K E
  have h₂E : (2 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₂
  have h₃E : (3 : E) ≠ 0 := by simpa only [map_ofNat] using (map_ne_zero i).mpr h₃
  have hAE : i A ≠ 0 := (map_ne_zero i).mpr hA
  have hCard := Module.card_eq_pow_finrank (K := K) (V := E)
  obtain ⟨ht, hd⟩ := coefficients_at_extension K E L 12 A (Module.finrank K E) hCard
  obtain ⟨htE, hdE⟩ := CubicFrobeniusModTwelve.trace_det E L h₂E h₃E hAE
  exact ⟨ht.trans htE, hd.trans hdE⟩

end
end ManuscriptAudit.CubicFrobeniusResidueExtensions

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicFrobeniusResidueExtensions.trace_det_power_eq_extension_count
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
