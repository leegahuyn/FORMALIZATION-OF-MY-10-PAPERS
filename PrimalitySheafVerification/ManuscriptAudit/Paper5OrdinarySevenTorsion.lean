import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import PrimalitySheafVerification.ManuscriptAudit.Paper5OrdinarySevenGeometry

/-!
# The actual geometric torsion group has seven points

Every geometric seven-torsion point of the good ordinary fiber in
Paper 5 already lies over the residue field. Its group thus has
order seven, contrary to the order forty-nine in the blanket
ordinary-fiber assertion on physical pp. 161–162.
-/

namespace ManuscriptAudit.Paper5OrdinarySevenTorsion

open WeierstrassCurve ManuscriptAudit.Paper5OrdinarySeven
open ManuscriptAudit.Paper5OrdinarySevenGeometry

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev baseCurve : Affine (ZMod 7) := (ordinaryCurve (ZMod 7)).toAffine

private abbrev PointsAt (L : Type*) [Field L] [Algebra (ZMod 7) L] :=
  (baseCurve.baseChange L).Point

variable (L : Type*) [Field L] [DecidableEq L] [Algebra (ZMod 7) L]

local instance : CharP L 7 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 7) L).injective 7

private theorem baseCurve_baseChange : baseCurve.baseChange L = (ordinaryCurve L).toAffine := by
  simp [baseCurve, ordinaryCurve, WeierstrassCurve.baseChange, WeierstrassCurve.map, map_ofNat]

abbrev SevenTorsion := {P : PointsAt L // (7 : ℕ) • P = 0}

private def pointMap : PointsAt (ZMod 7) →+ PointsAt L :=
  Affine.Point.map (W' := baseCurve) (Algebra.ofId (ZMod 7) L)

private theorem rational_model_card : Nat.card (PointsAt (ZMod 7)) = 7 := by
  change Nat.card (baseCurve.baseChange (ZMod 7)).Point = 7
  rw [baseCurve_baseChange]
  exact rational_affine_card

private theorem field_torsion_coordinates :
    ∀ (x y : L) (h : (baseCurve.baseChange L).Nonsingular x y),
      (7 : ℕ) • (.some x y h : PointsAt L) = 0 →
        (x = 3 ∨ x = 5 ∨ x = 6) ∧ (y = 2 ∨ y = 5) := by
  rw [baseCurve_baseChange L]
  intro x y h hP
  exact seven_torsion_coordinates L hP

private theorem torsion_descends (P : PointsAt L) (hP : (7 : ℕ) • P = 0) :
    ∃ Q : PointsAt (ZMod 7), pointMap L Q = P := by
  cases P with
  | zero => exact ⟨0, (pointMap L).map_zero⟩
  | some x y h =>
    let f := Algebra.ofId (ZMod 7) L
    obtain ⟨hx, hy⟩ := field_torsion_coordinates L x y h hP
    have hx' : ∃ a : ZMod 7, f a = x := by
      rcases hx with rfl | rfl | rfl
      · exact ⟨3, by simp [f]⟩
      · exact ⟨5, by simp [f]⟩
      · exact ⟨6, by simp [f]⟩
    have hy' : ∃ b : ZMod 7, f b = y := by
      rcases hy with rfl | rfl
      · exact ⟨2, by simp [f]⟩
      · exact ⟨5, by simp [f]⟩
    obtain ⟨a, ha⟩ := hx'
    obtain ⟨b, hb⟩ := hy'
    have hr : (baseCurve.baseChange (ZMod 7)).Nonsingular a b :=
      (baseCurve.baseChange_nonsingular (f := f) f.injective a b).mp
        (by simpa only [ha, hb] using h)
    refine ⟨.some a b hr, ?_⟩
    change Affine.Point.map (W' := baseCurve) f (.some a b hr) = _
    simp only [Affine.Point.map_some, Affine.Point.some.injEq, ha, hb, and_self]

private def restrictPointMap : PointsAt (ZMod 7) → SevenTorsion L :=
  fun Q => ⟨pointMap L Q, by
    have hQ : (7 : ℕ) • Q = 0 := by
      have ht : Nat.card (PointsAt (ZMod 7)) • Q = 0 := card_nsmul_eq_zero'
      simpa only [rational_model_card] using ht
    rw [← map_nsmul, hQ, map_zero]⟩

/-- The rational point group exhausts the seven-torsion over any extension. -/
def sevenTorsionEquiv : PointsAt (ZMod 7) ≃ SevenTorsion L :=
  Equiv.ofBijective (restrictPointMap L) ⟨by
    intro P Q h
    exact Affine.Point.map_injective (W' := baseCurve) (Algebra.ofId (ZMod 7) L)
      (congrArg Subtype.val h), by
    rintro ⟨P, hP⟩
    obtain ⟨Q, hQ⟩ := torsion_descends L P hP
    exact ⟨Q, Subtype.ext hQ⟩⟩

theorem seven_torsion_cardinal : Nat.card (SevenTorsion L) = 7 :=
  (Nat.card_congr (sevenTorsionEquiv L)).symm.trans rational_model_card

private abbrev GeometricField := AlgebraicClosure (ZMod 7)
private abbrev GeometricCurve := (ordinaryCurve (ZMod 7)).baseChange GeometricField

abbrev GeometricSevenTorsion :=
  {P : GeometricCurve.toProjective.Point // (7 : ℕ) • P = 0}

theorem geometric_projective_seven_torsion_cardinal :
    Nat.card GeometricSevenTorsion = 7 := by
  classical
  let e : GeometricCurve.toProjective.Point ≃+ PointsAt GeometricField :=
    Projective.Point.toAffineAddEquiv (W := GeometricCurve.toProjective)
  let t : GeometricSevenTorsion ≃ SevenTorsion GeometricField :=
    { toFun := fun P => ⟨e P, by rw [← map_nsmul, P.2, map_zero]⟩
      invFun := fun P => ⟨e.symm P, by rw [← map_nsmul, P.2, map_zero]⟩
      left_inv := fun P => Subtype.ext (e.symm_apply_apply P)
      right_inv := fun P => Subtype.ext (e.apply_symm_apply P) }
  exact (Nat.card_congr t).trans (seven_torsion_cardinal GeometricField)

/-- The native geometric seven-torsion cannot have rank two over \(\mathbf F_7\). -/
theorem paper5_ordinary_geometric_seven_torsion_not_rank_two :
    ¬ Nonempty (GeometricSevenTorsion ≃ (ZMod 7 × ZMod 7)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e
  rw [geometric_projective_seven_torsion_cardinal, Nat.card_eq_fintype_card,
    Fintype.card_prod, ZMod.card] at hc
  exact (by decide : (7 : ℕ) ≠ 7 * 7) hc

end

end ManuscriptAudit.Paper5OrdinarySevenTorsion

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.Paper5OrdinarySevenTorsion.sevenTorsionEquiv,
      ``ManuscriptAudit.Paper5OrdinarySevenTorsion.seven_torsion_cardinal,
      ``ManuscriptAudit.Paper5OrdinarySevenTorsion.geometric_projective_seven_torsion_cardinal,
      ``ManuscriptAudit.Paper5OrdinarySevenTorsion.paper5_ordinary_geometric_seven_torsion_not_rank_two] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
