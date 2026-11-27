import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicRotationModFourTraceKernel
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitFrobeniusModFourDeterminant
import PrimalitySheafVerification.ManuscriptAudit.CubicQuadraticTwistFixedTorsion

/-! Native mod-four trace alternatives in terms of the rational two-torsion and cube fixed counts. -/

namespace ManuscriptAudit.CubicSplitModFourTracePatterns

open Module CubicThreeTorsionOrdinate CubicTwoPowerTorsion CubicNonsplitThreeAdicTrace
open CubicRotationModFourTraceKernel CubicSplitTwoPowerFrobenius
open CubicSplitFrobeniusModFourPatterns TorsionFrobeniusModule

noncomputable section

private def includeTwo {G : Type*} [AddCommGroup G] (P : Torsion 2 G) : Torsion 4 G :=
  ⟨P.val, by
    have h : (2 : ℕ) • P.val = 0 := P.property
    change (4 : ℕ) • P.val = 0
    rw [show (4 : ℕ) = 2 * 2 by decide, mul_nsmul', h, nsmul_zero]⟩

private theorem fixed_iff_includeTwo {G : Type*} [AddCommGroup G] (f : AddMonoid.End G)
    (P : Torsion 2 G) :
    mapLinear 2 f P = P ↔ mapLinear 4 f (includeTwo P) = includeTwo P := by
  constructor
  · intro h
    exact Subtype.ext (congrArg (fun Q : Torsion 2 G => Q.val) h)
  · intro h
    exact Subtype.ext (congrArg (fun Q : Torsion 4 G => Q.val) h)

variable (K L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field L] [IsAlgClosed L] [Algebra K L] [DecidableEq L]

theorem rational_trace_patterns {A z : K} (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0)
    (hA : A ≠ 0) (hz : IsPrimitiveRoot z 3) (hq : (Fintype.card K : ZMod 4) = 1) :
    let F := levelFrobenius K L A 2
    let t := LinearMap.trace (ZMod 4) (Level K L A 2) F
    let c := Nat.card (Torsion 2 (Curve A).Point)
    (t = 2 ∧ c = 4) ∨
    (t = 1 ∧ c = 1 ∧ Nat.card {x : Level K L A 2 // (F ^ 3) x = x} = 4) ∨
    (t = 3 ∧ c = 1 ∧ Nat.card {x : Level K L A 2 // (F ^ 3) x = x} = 16) := by
  let G := GeometricPoints K L A
  let f := arithmeticPointFrobenius K L A
  let F := levelFrobenius K L A 2
  let S := levelRotation K L h₂ h₃ hA hz 2
  have hd : LinearMap.det F = 1 := (CubicSplitFrobeniusModFourDeterminant.native_determinant_eq_card
    K L h₂ h₃ hA hz).trans hq
  obtain ⟨B, hB₀, hB₁, a, b, hF⟩ := exists_native_rotation_form K L h₂ h₃ hA hz
  have hPat := trace_fixed_patterns B S F hB₀ hB₁ a b hF hd
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  have hGeo : Nat.card (Torsion 2 G) = 4 :=
    (Nat.card_congr (carrierEquiv 2 G)).trans (affine_twoPower_card h₂L h₃L hAL 1)
  have hRat := CubicQuadraticTwistFixedTorsion.rational_torsion_card K L 2 A
  have hAnn (P : Torsion 2 G) : (2 : ℕ) • includeTwo P = 0 := Subtype.ext P.property
  have hTrivial (h : ∀ P : Torsion 4 G, (2 : ℕ) • P = 0 → F P = P → P = 0) :
      Nat.card (Torsion 2 (Curve A).Point) = 1 := by
    rw [hRat]
    apply Nat.card_eq_one_iff_exists.mpr
    refine ⟨⟨0, map_zero _⟩, fun P => Subtype.ext ?_⟩
    have hP := h (includeTwo P.val) (hAnn P.val)
      ((fixed_iff_includeTwo f P.val).mp P.property)
    exact Subtype.ext (congrArg (fun Q : Torsion 4 G => Q.val) hP)
  rcases hPat with ⟨ht, hAll⟩ | ⟨ht, hOnlyZero, hCard⟩ | ⟨ht, hOnlyZero, hCard⟩
  · apply Or.inl
    refine ⟨ht, hRat.trans ?_⟩
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv (fun P : Torsion 2 G =>
      (fixed_iff_includeTwo f P).mpr (hAll (includeTwo P) (hAnn P))))).trans hGeo
  · exact Or.inr (Or.inl ⟨ht, hTrivial hOnlyZero, hCard⟩)
  · exact Or.inr (Or.inr ⟨ht, hTrivial hOnlyZero, hCard⟩)

end
end ManuscriptAudit.CubicSplitModFourTracePatterns

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicSplitModFourTracePatterns.rational_trace_patterns
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
