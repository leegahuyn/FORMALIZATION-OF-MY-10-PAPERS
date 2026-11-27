import Lean.Util.CollectAxioms
import Lean.Elab.Tactic.Omega
import PrimalitySheafVerification.ManuscriptAudit.CubicLangSurjective
import PrimalitySheafVerification.ManuscriptAudit.CubicExtensionFrobeniusAt
import PrimalitySheafVerification.ManuscriptAudit.CubicSplitPrimeFixedCounts

/-! Lang surjectivity holds for every positive arithmetic Frobenius power over a good prime field. -/

namespace ManuscriptAudit.CubicLangPowers

open Polynomial WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicNonsplitThreeAdicTrace Paper5NonsplitFrobeniusModFour

noncomputable section
open scoped Classical

private theorem lang_at (E L : Type*) [Field E] [Fintype E] [Field L] [DecidableEq L]
    [IsAlgClosed L] [Algebra E L] (h₂ : (2 : E) ≠ 0) (h₃ : (3 : E) ≠ 0)
    (hchar : ringChar E ≠ 2) {a : E} (ha : a ≠ 0)
    (V : Affine L) (hV : Curve (algebraMap E L a) = V) :
    Function.Surjective (⇑(pointMapAt E L (Curve a) V
      ((centered_baseChange E L a).trans hV) (FiniteField.frobeniusAlgHom E L) - 1 :
      AddMonoid.End V.Point)) := by
  subst V
  exact CubicLangSurjective.surjective E L h₂ h₃ hchar ha

variable (p : ℕ) [Fact p.Prime] (L : Type*) [Field L] [Algebra (ZMod p) L]
  [DecidableEq L] [IsAlgClosed L]

/-- Each positive arithmetic Frobenius power minus identity is the surjective Lang map
over an actual finite extension embedded into the given algebraically closed field. -/
theorem pow_sub_one_surjective (hp : 5 ≤ p) {A : ZMod p} (hA : A ≠ 0)
    {n : ℕ} (hn : 0 < n) :
    Function.Surjective (⇑(arithmeticPointFrobenius (ZMod p) L A ^ n - 1 :
      AddMonoid.End (GeometricPoints (ZMod p) L A))) := by
  let E := GaloisField p n
  letI : Fintype E := Fintype.ofFinite E
  have hDegree : Module.finrank (ZMod p) E = n := GaloisField.finrank p hn.ne'
  letI : Algebra.IsAlgebraic (ZMod p) E := ⟨fun x => ⟨
    (X ^ Fintype.card E - X : (ZMod p)[X]),
    FiniteField.X_pow_card_sub_X_ne_zero (ZMod p) Fintype.one_lt_card,
    by simp [FiniteField.pow_card]⟩⟩
  let i : E →ₐ[ZMod p] L := IsAlgClosed.lift
  letI : Algebra E L := i.toRingHom.toAlgebra
  have hA' : algebraMap E L (algebraMap (ZMod p) E A) = algebraMap (ZMod p) L A := i.commutes A
  have hCard : Fintype.card E = (Fintype.card (ZMod p)) ^ n := by
    rw [← hDegree]
    exact Module.card_eq_pow_finrank
  have hpow := CubicExtensionFrobeniusAt.point_eq_pow (ZMod p) E L n A hA' hCard
  obtain ⟨h₂K, h₃K⟩ := small_char p (ZMod p) hp
  have h₂ : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₂K
  have h₃ : (3 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero (algebraMap (ZMod p) E)).mpr h₃K
  have hchar : ringChar E ≠ 2 := by
    intro h
    exact h₂ ((ringChar.spec E 2).mpr (by simpa only [h] using (dvd_rfl : (2 : ℕ) ∣ 2)))
  rw [← hpow]
  exact lang_at E L h₂ h₃ hchar ((map_ne_zero (algebraMap (ZMod p) E)).mpr hA)
    (Curve (algebraMap (ZMod p) L A)) (congrArg Curve hA')

end

end ManuscriptAudit.CubicLangPowers

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CubicLangPowers.pow_sub_one_surjective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
