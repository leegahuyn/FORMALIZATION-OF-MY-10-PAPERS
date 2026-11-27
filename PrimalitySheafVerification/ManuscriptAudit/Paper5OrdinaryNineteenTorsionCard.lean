import Lean.Util.CollectAxioms
import Mathlib.SetTheory.Cardinal.NatCard
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinates
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinaryNineteenTorsionCoordinateCard

/-! The ordinary characteristic-nineteen cubic has exactly nineteen geometric nineteen-torsion points. -/

namespace ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard

open WeierstrassCurve FiniteFieldPointCount CubicThreeTorsionOrdinate
open Paper5OrdinaryNineteenCoordinates Paper5OrdinaryNineteenTorsionCoordinates
open Paper5OrdinaryNineteenTorsionAlgebra Paper5OrdinaryNineteenTorsionCoordinateCard

noncomputable section

variable (L : Type*) [Field L] [Algebra (ZMod 19) L] [CharP L 19] [IsAlgClosed L] [DecidableEq L]

abbrev Torsion := {P : Points L // (19 : ℕ) • P = 0}

def coordinateEquiv : Torsion L ≃ Option (Coordinates L) where
  toFun
    | ⟨.zero, _⟩ => none
    | ⟨.some x y h, hp⟩ =>
      some ⟨⟨x ^ 3, (torsion_some_iff L h).mp hp⟩, ⟨x, rfl⟩,
        ⟨y, (nonsingular_iff (discriminant_ne_zero L) x y).mp h⟩⟩
  invFun
    | none => ⟨0, nsmul_zero _⟩
    | some ⟨t, x, y⟩ =>
      let he : (y : L) ^ 2 = (x : L) ^ 3 + 1 :=
        y.property.trans (congrArg (fun z : L => z + 1) x.property.symm)
      let h := (nonsingular_iff (discriminant_ne_zero L) x y).mpr he
      let ht : torsionCubic ((x : L) ^ 3) = 0 :=
        (congrArg torsionCubic x.property).trans t.property
      ⟨Affine.Point.some x y h, (torsion_some_iff L h).mpr ht⟩
  left_inv P := by
    rcases P with ⟨P, hP⟩
    cases P <;> rfl
  right_inv c := by
    cases c with
    | none => rfl
    | some c =>
      rcases c with ⟨⟨t, ht⟩, ⟨x, hx⟩, ⟨y, hy⟩⟩
      change x ^ 3 = t at hx
      subst t
      rfl

theorem affine_card : Nat.card (Torsion L) = 19 := by
  have h := coordinates_card L
  letI : Finite (Coordinates L) := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  letI : Fintype (Coordinates L) := Fintype.ofFinite _
  rw [Nat.card_congr (coordinateEquiv L), Nat.card_eq_fintype_card, Fintype.card_option,
    ← Nat.card_eq_fintype_card, h]

theorem projective_card :
    Nat.card {P : (shortCubic (0 : L) 1).toProjective.Point // (19 : ℕ) • P = 0} = 19 := by
  let e : (shortCubic (0 : L) 1).toProjective.Point ≃+ Points L :=
    Projective.Point.toAffineAddEquiv ((shortCubic (0 : L) 1).toProjective)
  let E : {P : (shortCubic (0 : L) 1).toProjective.Point // (19 : ℕ) • P = 0} ≃ Torsion L :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.property, map_zero]⟩
      invFun := fun P => ⟨e.symm P, by rw [← map_nsmul, P.property, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P => Subtype.ext (e.apply_symm_apply P) }
  exact (Nat.card_congr E).trans (affine_card L)

end
end ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard.coordinateEquiv,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard.affine_card,
      ``ManuscriptAudit.Paper5OrdinaryNineteenTorsionCard.projective_card] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
