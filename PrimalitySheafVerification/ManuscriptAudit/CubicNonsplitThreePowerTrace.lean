import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicNonsplitFrobeniusTrace
import PrimalitySheafVerification.ManuscriptAudit.CubicThreePowerTorsion

/-! Actual Frobenius trace in the nonsplit family modulo every power of three. -/

namespace ManuscriptAudit.CubicNonsplitThreePowerTrace

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate CubicThreeTorsionCard
open CubicCubeRotation CubicRotationQuadratic CubicThreeRotationCyclicBasis CubicThreePowerTorsion
open CubicNonsplitFrobeniusTrace CubicThreeFrobeniusSigns CubicThreePointCounts
open CyclotomicConjugationTrace TorsionFrobeniusModule PowerTorsionTower

noncomputable section

variable (E : Type*) [Field E] [Fintype E]
variable (L : Type*) [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

abbrev action (A : E) (n : ℕ) :
    Module.End (ZMod (3 ^ n)) (PowerTorsion 3 ((Curve A).baseChange L).Point n) :=
  pointMap (3 ^ n) (Curve A) (FiniteField.frobeniusAlgHom E L)

/-- The native q-power point map has trace zero on all three-power levels when q≡2 mod 3. -/
theorem actual_trace_zero {A : E}
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) (n : ℕ) :
    LinearMap.trace (ZMod (3 ^ n)) (PowerTorsion 3 ((Curve A).baseChange L).Point n)
      (action E L A n) = 0 := by
  cases n with
  | zero =>
    letI : Subsingleton (ZMod (3 ^ 0)) := inferInstanceAs (Subsingleton (ZMod 1))
    exact Subsingleton.elim _ _
  | succ n =>
    let a := algebraMap E L A
    have h₂L : (2 : L) ≠ 0 := by
      have h := (map_ne_zero (algebraMap E L)).mpr h₂
      simpa only [map_ofNat] using h
    have h₃L : (3 : L) ≠ 0 := by
      have h := (map_ne_zero (algebraMap E L)).mpr h₃
      simpa only [map_ofNat] using h
    have ha : a ≠ 0 := (map_ne_zero (algebraMap E L)).mpr hA
    let hΔ := shortCubic_discriminant_ne_zero h₂L h₃L ha
    let he := centered_baseChange E L A
    let g := FiniteField.frobeniusAlgHom E L
    obtain ⟨z, hz, hz₁⟩ := exists_nontrivial_cubeRoot h₃L
    have hg : g z = z ^ 2 := by
      change z ^ Fintype.card E = _
      rw [pow_cube_reduce z _ hz, hq]
    let G := (Curve a).Point
    let m := 3 ^ (n + 1)
    let f := pointMapAt E L (Curve A) (Curve a) he g
    let S := mapLinear m (rotate z hz hΔ)
    let F := mapLinear m f
    obtain ⟨B, hStep⟩ := exists_cyclic_basis h₂L h₃L ha hz hz₁ n
    change S (B 0) = B 1 at hStep
    have hCube : S (S (S (B 0))) = B 0 :=
      Subtype.ext (rotate_cube hz hΔ (B 0 : G))
    have hQ := rotation_linear_quad m h₂L h₃L ha hz hz₁ hΔ (B 0)
    change S (S (B 0)) + S (B 0) + B 0 = 0 at hQ
    rw [hStep] at hQ
    have hQuad : S (S (B 0)) = -B 0 - B 1 :=
      (eq_sub_iff_add_eq).mpr (eq_neg_of_add_eq_zero_left hQ)
    have hConj : F (S (B 0)) = S (S (F (B 0))) := Subtype.ext
      (pointMapAt_conjugates_rotation E L (Curve A) he g hg hz hΔ (B 0 : G))
    have ht := (trace_det_of_cycle B S F hStep hCube hQuad hConj).1
    let e := torsionTransport L m he
    rw [← LinearMap.trace_conj' _ e]
    change LinearMap.trace (ZMod m) (Torsion m G) (e.conj (pointMap m (Curve A) g)) = 0
    rw [mapLinear_transport E L (Curve A) (Curve a) he g]
    exact ht

theorem actual_trace_eq_signed_point_count {A : E} [DecidableEq E]
    (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0) (hA : A ≠ 0)
    (hq : Fintype.card E % 3 = 2) (n : ℕ) :
    LinearMap.trace (ZMod (3 ^ n)) (PowerTorsion 3 ((Curve A).baseChange L).Point n)
      (action E L A n) =
      (((Fintype.card E : ℤ) + 1 -
        (Nat.card (shortCubic (0 : E) A).toProjective.Point : ℤ)) : ZMod (3 ^ n)) := by
  rw [actual_trace_zero E L h₂ h₃ hA hq n, projective_count_residue_two A h₂ h₃ hA hq]
  simp [Nat.cast_add]

end
end ManuscriptAudit.CubicNonsplitThreePowerTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicNonsplitThreePowerTrace.actual_trace_zero,
      ``ManuscriptAudit.CubicNonsplitThreePowerTrace.actual_trace_eq_signed_point_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
