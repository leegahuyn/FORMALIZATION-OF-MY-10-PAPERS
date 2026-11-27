import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticKummerSquareClasses
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitProductCoordinates

/-! The arithmetic binary H¹ of the actual Laurent line over any finite odd field. -/

namespace ManuscriptAudit.ArithmeticLaurentBinary

open AlgebraicGeometry CategoryTheory LaurentPolynomial
open ArithmeticKummerSquareClasses KummerPIDUnitQuotient LaurentUnitProductCoordinates

noncomputable section

attribute [local instance] SmallEtaleCohomologyComparison.fullSiteHasExt

variable (K : Type) [Field K]

private abbrev scalarClasses := Additive Kˣ ⧸ powerSubgroup K 2

private def pairReduction : Additive Kˣ × ℤ →+ scalarClasses K × ZMod 2 :=
  (QuotientAddGroup.mk' (powerSubgroup K 2)).prodMap (Int.castAddHom (ZMod 2))

private theorem ofMul_square {G : Type*} [Monoid G] (u : G) :
    Additive.ofMul (u ^ (2 : ℕ)) = 2 • Additive.ofMul u := by
  rw [two_nsmul, pow_two]
  rfl

private theorem pairReduction_surjective : Function.Surjective (pairReduction K) := by
  intro x
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective x.1
  obtain ⟨n, hn⟩ := ZMod.intCast_surjective x.2
  exact ⟨(a, n), Prod.ext ha hn⟩

private theorem pairReduction_eq_zero_iff (x : Additive Kˣ × ℤ) :
    pairReduction K x = 0 ↔ ∃ y : Additive Kˣ × ℤ, 2 • y = x := by
  constructor
  · intro h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    change (x.1 : scalarClasses K) = 0 at h₁
    change (x.2 : ZMod 2) = 0 at h₂
    obtain ⟨u, hu⟩ := (mem_powerSubgroup 2 x.1).mp ((QuotientAddGroup.eq_zero_iff x.1).mp h₁)
    obtain ⟨n, hn⟩ := (CharP.intCast_eq_zero_iff (ZMod 2) 2).mp h₂
    refine ⟨(Additive.ofMul u, n), Prod.ext ?_ ?_⟩
    · change 2 • Additive.ofMul u = x.1
      exact (ofMul_square u).symm.trans (congrArg Additive.ofMul hu)
    · change (2 : ℕ) • n = x.2
      rw [two_nsmul, ← two_mul]
      exact hn.symm
  · rintro ⟨y, rfl⟩
    apply Prod.ext
    · change ((2 • y.1 : Additive Kˣ) : scalarClasses K) = 0
      apply (QuotientAddGroup.eq_zero_iff _).mpr
      apply (mem_powerSubgroup 2 _).mpr
      exact ⟨y.1.toMul, congrArg Additive.toMul (ofMul_square y.1.toMul)⟩
    · change (((2 : ℕ) • y.2 : ℤ) : ZMod 2) = 0
      apply (CharP.intCast_eq_zero_iff (ZMod 2) 2).mpr
      exact ⟨y.2, by rw [two_nsmul, two_mul] <;> rfl⟩

private def unitReduction : Additive (LaurentPolynomial K)ˣ →+ scalarClasses K × ZMod 2 :=
  (pairReduction K).comp (unitCoordinates K).symm.toAddMonoidHom

private theorem unitReduction_ker :
    (unitReduction K).ker = powerSubgroup (LaurentPolynomial K) 2 := by
  ext u
  rw [AddMonoidHom.mem_ker, mem_powerSubgroup]
  change pairReduction K ((unitCoordinates K).symm u) = 0 ↔ _
  rw [pairReduction_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    let v := unitCoordinates K y
    have h : 2 • v = u := by
      have h' := congrArg (unitCoordinates K) hy
      simpa only [map_nsmul, AddEquiv.apply_symm_apply] using h'
    refine ⟨v.toMul, ?_⟩
    exact congrArg Additive.toMul ((ofMul_square v.toMul).trans h)
  · rintro ⟨v, hv⟩
    refine ⟨(unitCoordinates K).symm (Additive.ofMul v), ?_⟩
    have he : 2 • Additive.ofMul v = u :=
      (ofMul_square v).symm.trans (congrArg Additive.ofMul hv)
    rw [← map_nsmul, he]

def unitSquareClassesEquiv :
    (Additive (LaurentPolynomial K)ˣ ⧸ powerSubgroup (LaurentPolynomial K) 2) ≃+
      scalarClasses K × ZMod 2 :=
  (QuotientAddGroup.quotientAddEquivOfEq (unitReduction_ker K).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (unitReduction K)
      ((pairReduction_surjective K).comp (unitCoordinates K).symm.surjective))

def laurentBinaryHOneEquiv [Finite K] (h₂ : (2 : K) ≠ 0) :
    (ZMod 2 × ZMod 2) ≃+
      Sheaf.H ((constantSheaf (Spec (CommRingCat.of (LaurentPolynomial K))).smallEtaleTopology
        AddCommGrpCat.{0}).obj (AddCommGrpCat.of (ZMod 2))) 1 := by
  let e := (residueBinaryHOneEquiv K h₂).trans (squareClassHOneEquiv K K h₂).symm
  exact (e.prodCongr (AddEquiv.refl (ZMod 2))).trans
    ((unitSquareClassesEquiv K).symm.trans (squareClassHOneEquiv K (LaurentPolynomial K) h₂))

end
end ManuscriptAudit.ArithmeticLaurentBinary

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ArithmeticLaurentBinary.unitSquareClassesEquiv,
      ``ManuscriptAudit.ArithmeticLaurentBinary.laurentBinaryHOneEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
