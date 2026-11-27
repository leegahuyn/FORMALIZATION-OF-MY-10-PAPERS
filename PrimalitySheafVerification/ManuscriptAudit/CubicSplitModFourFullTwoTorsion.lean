import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant

/-! Fourth-level trace when the rational two-torsion is full. -/

namespace ManuscriptAudit.CubicSplitModFourFullTwoTorsion

open Module CubicRotationModFourModel CubicRotationModFourKernel CubicRotationCentralizer
open FiniteFieldPointCount CubicThreeTorsionOrdinate CubicTwoPowerTorsion CubicNonsplitThreeAdicTrace
open CubicSplitTwoPowerFrobenius CubicSplitFrobeniusModFourPatterns
open CubicSplitFrobeniusModFourDeterminant CubicQuadraticTwistFixedTorsion TorsionFrobeniusModule

noncomputable section

private theorem model_relation :
    ∀ a b : ZMod 4, (∀ v : Coordinates, (2 : ℕ) • v = 0 → action a b v = v) →
      2 * a - b = norm a b + 1 := by decide

private theorem trace_relation {V : Type*} [AddCommGroup V] [Module (ZMod 4) V]
    (B : Basis (Fin 2) (ZMod 4) V) (S F : Module.End (ZMod 4) V)
    (h₀ : S (B 0) = B 1) (h₁ : S (B 1) = -B 0 - B 1)
    (a b : ZMod 4) (hF : F = a • 1 + b • S)
    (hFix : ∀ x : V, (2 : ℕ) • x = 0 → F x = x) :
    LinearMap.trace (ZMod 4) V F = LinearMap.det F + 1 := by
  letI : Fact (1 < (4 : ℕ)) := ⟨by decide⟩
  have hform := trace_det_of_form B S h₀ h₁ a b
  have hz (v : Coordinates) (hv : (2 : ℕ) • v = 0) : action a b v = v := by
    let x := (coordinates B).symm v
    have he : coordinates B x = v := (coordinates B).apply_symm_apply v
    have hx : (2 : ℕ) • x = 0 := (coordinates B).injective (by
      rw [map_nsmul, map_zero, he, hv])
    have h := coordinates_action B S h₀ h₁ a b x
    rw [← hF, hFix x hx, he] at h
    exact h.symm
  rw [hF, hform.1, hform.2, model_relation a b hz] <;> rfl

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [DecidableEq L] [Algebra K L]

/-- Actual mod-four trace and determinant differ by one whenever the centered split curve
has all four two-torsion points rational over the base. -/
theorem trace_eq_det_add_one {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (hRat : Nat.card (Torsion 2 (Curve A).Point) = 4) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      LinearMap.det (levelFrobenius K L A 2) + 1 := by
  let G := GeometricPoints K L A
  let f := arithmeticPointFrobenius K L A
  let S := levelRotation K L h₂ h₃ hA hz 2
  let F := levelFrobenius K L A 2
  obtain ⟨B, h₀, h₁, a, b, h⟩ := exists_native_rotation_form K L h₂ h₃ hA hz
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  have hGeo : Nat.card (Torsion 2 G) = 4 :=
    (Nat.card_congr (carrierEquiv 2 G)).trans (affine_twoPower_card h₂L h₃L hAL 1)
  letI : Finite (Torsion 2 G) := Nat.finite_of_card_ne_zero (by rw [hGeo]; decide)
  have hc : Nat.card {P : Torsion 2 G // mapLinear 2 f P = P} = 4 :=
    (rational_torsion_card K L 2 A).symm.trans hRat
  have he : Function.Surjective
      (Subtype.val : {P : Torsion 2 G // mapLinear 2 f P = P} → Torsion 2 G) :=
    (Subtype.val_injective.bijective_of_nat_card_le (by rw [hGeo, hc])).2
  have hFix (P : Level K L A 2) (hP : (2 : ℕ) • P = 0) : F P = P := by
    let Q : Torsion 2 G := ⟨P.val, congrArg (fun R : Torsion 4 G => R.val) hP⟩
    obtain ⟨R, hRQ⟩ := he Q
    have hQ : mapLinear 2 f Q = Q := hRQ ▸ R.property
    exact Subtype.ext (congrArg (fun R : Torsion 2 G => R.val) hQ)
  exact trace_relation B S F h₀ h₁ a b h hFix

/-- In the full rational two-torsion case, the native mod-four trace is the actual signed count. -/
theorem trace_eq_signed_count {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3)
    (hRat : Nat.card (Torsion 2 (Curve A).Point) = 4) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (((Fintype.card K : ℤ) + 1 -
        (Nat.card (shortCubic (0 : K) A).toProjective.Point : ℤ)) : ZMod 4) := by
  have hd : (4 : ℕ) ∣ Nat.card (Curve A).Point :=
    hRat ▸ QuadraticTwistModFourCount.torsion_card_dvd (G := (Curve A).Point) 2
  have hzero : (Nat.card (Curve A).Point : ZMod 4) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hd
  rw [trace_eq_det_add_one K L h₂ h₃ hA hz hRat,
    native_determinant_eq_card K L h₂ h₃ hA hz]
  simp only [Int.cast_sub, Int.cast_add, Int.cast_one, Int.cast_natCast,
    ← card_eq_projective A, hzero, sub_zero]

end
end ManuscriptAudit.CubicSplitModFourFullTwoTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitModFourFullTwoTorsion.trace_eq_det_add_one,
      ``ManuscriptAudit.CubicSplitModFourFullTwoTorsion.trace_eq_signed_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
