import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassGeneralFrobeniusTorsionFixed
import PrimalitySheafVerification.ManuscriptAudit.CubicQuadraticTwistFrobenius

/-! Rational torsion on a quadratic twist counts the negative geometric fixed points. -/

namespace ManuscriptAudit.CubicQuadraticTwistFixedTorsion

open FiniteFieldPointCount CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicFrobeniusSexticTwists TorsionFrobeniusModule

noncomputable section

private def fixedCongr {G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (m : ℕ) (e : G ≃+ H) (f : AddMonoid.End G) (g : AddMonoid.End H)
    (he : ∀ x : G, g (e x) = e (f x)) :
    {x : Torsion m G // mapLinear m f x = x} ≃
      {y : Torsion m H // mapLinear m g y = y} := by
  let T : Torsion m G ≃ Torsion m H :=
    { toFun := mapLinear m e.toAddMonoidHom
      invFun := mapLinear m e.symm.toAddMonoidHom
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.val) }
  apply T.subtypeEquiv
  intro x
  constructor
  · intro hx
    apply Subtype.ext
    change g (e x.val) = e x.val
    rw [he]
    exact congrArg e (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    apply e.injective
    change e (f x.val) = e x.val
    rw [← he]
    exact congrArg Subtype.val hx

variable (E L : Type*) [Field E] [Fintype E] [DecidableEq E]
  [Field L] [Algebra E L] [IsAlgClosed L] [DecidableEq L]

/-- Native rational torsion equals the fixed torsion of the actual arithmetic Frobenius. -/
theorem rational_torsion_card (m : ℕ) (A : E) :
    Nat.card (Torsion m (Curve A).Point) =
      Nat.card {P : Torsion m (Geometric E L A) //
        mapLinear m (arithmeticFrobenius E L A) P = P} := by
  exact Nat.card_congr (WeierstrassGeneralFrobeniusTorsionFixed.rationalTorsionEquiv
    m (Algebra.ofId E L) (FiniteField.frobeniusAlgHom E L) (fun _ => rfl)
    (Curve A) (Curve (algebraMap E L A)) (centered_baseChange E L A))

/-- The rational torsion points of the actual quadratic twist are counted by the
negative fixed points of the original geometric Frobenius. -/
theorem twist_rational_torsion_card (m : ℕ) {A d : E} (hA : A ≠ 0) (hd : ¬ IsSquare d)
    (hchar : ringChar E ≠ 2) {k : ℕ} (hq : Fintype.card E = 6 * k + 1)
    (hΔA : (shortCubic (0 : L) (algebraMap E L A)).Δ ≠ 0)
    (hΔB : (shortCubic (0 : L) (algebraMap E L (d ^ 3 * A))).Δ ≠ 0) :
    Nat.card (Torsion m (Curve (d ^ 3 * A)).Point) =
      Nat.card {P : Torsion m (Geometric E L A) //
        -mapLinear m (arithmeticFrobenius E L A) P = P} := by
  obtain ⟨e, he⟩ := CubicQuadraticTwistFrobenius.exists_neg_conjugacy E L hA hd hchar hq hΔA hΔB
  let f := arithmeticFrobenius E L A
  let g := arithmeticFrobenius E L (d ^ 3 * A)
  have hsign : mapLinear m (-f) = -(mapLinear m f) :=
    LinearMap.ext (fun _ => Subtype.ext rfl)
  calc
    _ = Nat.card {P : Torsion m (Geometric E L (d ^ 3 * A)) // mapLinear m g P = P} :=
      rational_torsion_card E L m (d ^ 3 * A)
    _ = Nat.card {P : Torsion m (Geometric E L A) // mapLinear m (-f) P = P} :=
      Nat.card_congr (fixedCongr m e (-f) g he).symm
    _ = _ := by rw [hsign]; rfl

end
end ManuscriptAudit.CubicQuadraticTwistFixedTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CubicQuadraticTwistFixedTorsion.rational_torsion_card,
      ``ManuscriptAudit.CubicQuadraticTwistFixedTorsion.twist_rational_torsion_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
