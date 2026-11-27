import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitModFourTracePatterns
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitTraceResidueArithmetic
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitExtensionTraceRecurrence

/-! The actual trace modulo four in the split case with field size one modulo four. -/

namespace ManuscriptAudit.CubicSplitFrobeniusModFourTrace

open CubicThreeTorsionOrdinate CubicNonsplitThreeAdicTrace CubicTwoPowerTorsion
open CubicSplitTwoPowerFrobenius CubicSplitFrobeniusModFourDeterminant
open CubicSplitCubicExtensionTorsion CubicSplitExtensionTraceRecurrence TorsionFrobeniusModule
open QuadraticTwistModFourCount Paper5PrintedRecurrence

noncomputable section

private theorem signedTrace_cast {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (m : ℕ) (A : K) :
    (signedTrace A : ZMod m) = (Fintype.card K : ZMod m) + 1 -
      (Nat.card (Curve A).Point : ZMod m) := by
  simp only [signedTrace, Int.cast_add, Int.cast_sub, Int.cast_natCast, Int.cast_one,
    ← card_eq_projective A]

private theorem odd_of_rational_two_card_one {G : Type*} [AddCommGroup G] [Finite G]
    (h : Nat.card (Torsion 2 G) = 1) : Nat.card G % 2 = 1 := by
  have hd : ¬ (2 : ℕ) ∣ Nat.card G := by
    intro hv
    obtain ⟨P, hP, h2⟩ :=
      (WeierstrassFrobeniusModTwo.two_dvd_card_iff_nonzero_two_torsion G).mp hv
    letI : Subsingleton (Torsion 2 G) := (Nat.card_eq_one_iff_unique.mp h).1
    exact hP (congrArg (fun R : Torsion 2 G => R.val)
      (Subsingleton.elim (⟨P, h2⟩ : Torsion 2 G) 0))
  omega

private theorem signedTrace_odd {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (A : K) (hq : (Fintype.card K : ZMod 4) = 1)
    (h : Nat.card (Torsion 2 (Curve A).Point) = 1) :
    (signedTrace A : ZMod 2) = 1 := by
  letI : Finite (Curve A).Point := finite_points A
  have hq₄ := (ZMod.natCast_eq_natCast_iff' (Fintype.card K) 1 4).mp hq
  have hq₂ : (Fintype.card K : ZMod 2) = 1 :=
    (ZMod.natCast_eq_natCast_iff' (Fintype.card K) 1 2).mpr (by omega)
  have hC : (Nat.card (Curve A).Point : ZMod 2) = 1 :=
    (ZMod.natCast_eq_natCast_iff' _ 1 2).mpr (odd_of_rational_two_card_one h)
  rw [signedTrace_cast 2 A, hq₂, hC] <;> decide

variable (K E L : Type*) [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Fintype E] [DecidableEq E] [Field L] [IsAlgClosed L] [DecidableEq L]
  [Algebra K E] [Algebra K L] [Algebra E L]

theorem trace_eq_count_of_cubic_extension {A z : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : IsPrimitiveRoot z 3) (hq : (Fintype.card K : ZMod 4) = 1)
    (hCompat : algebraMap E L (algebraMap K E A) = algebraMap K L A)
    (hDegree : Module.finrank K E = 3) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (signedTrace A : ZMod 4) := by
  let a := algebraMap K E A
  let q := Fintype.card K
  let F := levelFrobenius K L A 2
  let f := arithmeticPointFrobenius K L A
  have hCard : Fintype.card E = q ^ 3 := by
    rw [Module.card_eq_pow_finrank (K := K) (V := E), hDegree]
  have hzdiv : 3 ∣ q - 1 := by
    rw [hz.eq_orderOf]
    exact orderOf_dvd_of_pow_eq_one
      (FiniteField.pow_card_sub_one_eq_one z (hz.ne_zero (by decide)))
  have hrec := extension_trace_eq_recurrence (E := E) h₂ h₃ hA hzdiv
  rw [hDegree] at hrec
  have hcubic : signedTrace a = signedTrace A ^ 3 - 3 * (q : ℤ) * signedTrace A := by
    rw [show signedTrace a = _ from hrec]
    simp only [recurrence]
    ring
  have hcount : ((signedTrace A ^ 3 - 3 * (q : ℤ) * signedTrace A : ℤ) : ZMod 8) =
      (q : ZMod 8) ^ 3 + 1 - (Nat.card (Curve a).Point : ZMod 8) := by
    rw [← hcubic, signedTrace_cast 8 a, hCard, Nat.cast_pow]
  have hR := CubicSplitModFourTracePatterns.rational_trace_patterns K L h₂ h₃ hA hz hq
  have hC4 := cubic_extension_count K E L 4 hCompat hCard
  have hC2 := cubic_extension_count K E L 2 hCompat hCard
  have h₂L : (2 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₂
  have h₃L : (3 : L) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap K L)).mpr h₃
  have hAL : algebraMap K L A ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hA
  have hGeom : Nat.card (Torsion 2 (GeometricPoints K L A)) = 4 :=
    (Nat.card_congr (carrierEquiv 2 _)).trans (affine_twoPower_card h₂L h₃L hAL 1)
  have hFix :=
    (CubicSplitFrobeniusModFourPatterns.native_cube_fixed_patterns K L h₂ h₃ hA hz).1
  have hC2' : Nat.card (Torsion 2 (Curve a).Point) = 4 := by
    refine hC2.trans ?_
    exact (Nat.card_congr (Equiv.subtypeUnivEquiv
      (fun P => (fix_two_of_four f hFix P).1))).trans hGeom
  letI : Finite (Curve a).Point := finite_points a
  rcases hR with ⟨ht, h2⟩ | ⟨ht, h2, h4⟩ | ⟨ht, h2, h4⟩
  · have hdiv : (4 : ℕ) ∣ Nat.card (Curve A).Point := h2 ▸ torsion_card_dvd 2
    have hzero := (ZMod.natCast_eq_zero_iff (Nat.card (Curve A).Point) 4).mpr hdiv
    rw [ht, signedTrace_cast 4 A, hq, hzero] <;> decide
  · have hsmall : (Nat.card (Curve a).Point : ZMod 8) = 4 :=
      (ZMod.natCast_eq_natCast_iff' _ 4 8).mpr
        (card_mod_eight_of_torsion_four hC2' (hC4.trans h4))
    have htrace8 := hcount.trans (show
      (q : ZMod 8) ^ 3 + 1 - (Nat.card (Curve a).Point : ZMod 8) = (q : ZMod 8) ^ 3 - 3 by
        rw [hsmall]
        ring)
    exact ht.trans (((CubicSplitTraceResidueArithmetic.trace_mod_four_of_third_trace q
      (signedTrace A) hq (signedTrace_odd A hq h2)).2 htrace8).symm)
  · have hfull : (Nat.card (Curve a).Point : ZMod 8) = 0 :=
      (ZMod.natCast_eq_natCast_iff' _ 0 8).mpr (card_mod_eight_of_torsion_sixteen (hC4.trans h4))
    have htrace8 := hcount.trans (show
      (q : ZMod 8) ^ 3 + 1 - (Nat.card (Curve a).Point : ZMod 8) = (q : ZMod 8) ^ 3 + 1 by
        rw [hfull, sub_zero])
    exact ht.trans (((CubicSplitTraceResidueArithmetic.trace_mod_four_of_third_trace q
      (signedTrace A) hq (signedTrace_odd A hq h2)).1 htrace8).symm)

/-- The actual trace on four-torsion equals the signed rational point count modulo four
for every split centered curve whose finite base has size one modulo four. -/
theorem native_trace_eq_count {A z : K}
    (h₂ : (2 : K) ≠ 0) (h₃ : (3 : K) ≠ 0) (hA : A ≠ 0)
    (hz : IsPrimitiveRoot z 3) (hq : (Fintype.card K : ZMod 4) = 1) :
    LinearMap.trace (ZMod 4) (Level K L A 2) (levelFrobenius K L A 2) =
      (signedTrace A : ZMod 4) := by
  classical
  let p := ringChar K
  letI : CharP K p := ringChar.charP K
  letI : Fact (Nat.Prime p) := ⟨CharP.char_is_prime K p⟩
  let E := FiniteField.Extension K p 3
  letI : Fintype E := Fintype.ofFinite E
  let i : E →ₐ[K] L := IsAlgClosed.lift
  letI : Algebra E L := i.toRingHom.toAlgebra
  have hCompat : algebraMap E L (algebraMap K E A) = algebraMap K L A := i.commutes A
  exact trace_eq_count_of_cubic_extension K E L h₂ h₃ hA hz hq hCompat
    (FiniteField.finrank_extension K p 3)

end
end ManuscriptAudit.CubicSplitFrobeniusModFourTrace

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicSplitFrobeniusModFourTrace.trace_eq_count_of_cubic_extension,
      ``ManuscriptAudit.CubicSplitFrobeniusModFourTrace.native_trace_eq_count] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
