import Lean.Util.CollectAxioms
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Ring

/-! The Y-chart equation of the projective node is a localization of a polynomial line. -/

namespace ManuscriptAudit.NodalYChartAlgebra

open Polynomial

noncomputable section

variable {R : Type*} [CommRing R]

private def linearEquation (u v : R) : R[X] := C u * X - C v
private abbrev LinCurve (u v : R) := AdjoinRoot (linearEquation u v)

private theorem root_relation (u v : R) :
    algebraMap R (LinCurve u v) u * AdjoinRoot.root (linearEquation u v) =
      algebraMap R (LinCurve u v) v := by
  have h := AdjoinRoot.mk_self (linearEquation u v)
  change AdjoinRoot.mk (linearEquation u v) (C u * X - C v) = 0 at h
  rw [map_sub, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_X, AdjoinRoot.mk_C,
    sub_eq_zero] at h
  exact h

private theorem image_isUnit {u v : R} (hc : ∃ a b : R, u * a + v * b = 1) :
    IsUnit (algebraMap R (LinCurve u v) u) := by
  obtain ⟨a, b, hb⟩ := hc
  let i := algebraMap R (LinCurve u v)
  let z := AdjoinRoot.root (linearEquation u v)
  let w := i a + i b * z
  have hw : i u * w = 1 := by
    calc
      _ = i u * i a + (i u * z) * i b := by dsimp [w]; ring
      _ = i u * i a + i v * i b := by rw [root_relation]
      _ = 1 := by rw [← map_mul, ← map_mul, ← map_add, hb, map_one]
  exact ⟨{ val := i u, inv := w, val_inv := hw, inv_val := by simpa [mul_comm] using hw }, rfl⟩

private def localizedRoot (u v : R) : Localization.Away u :=
  IsLocalization.Away.invSelf u * algebraMap R (Localization.Away u) v

private theorem localizedRoot_relation (u v : R) :
    (linearEquation u v).eval₂ (algebraMap R (Localization.Away u)) (localizedRoot u v) = 0 := by
  unfold linearEquation
  rw [eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, eval₂_C]
  unfold localizedRoot
  rw [← mul_assoc, IsLocalization.Away.mul_invSelf u, one_mul, sub_self]

private def toLocalization (u v : R) : LinCurve u v →ₐ[R] Localization.Away u :=
  AdjoinRoot.liftAlgHom (linearEquation u v) (Algebra.ofId R (Localization.Away u))
    (localizedRoot u v) (localizedRoot_relation u v)

private def fromLocalization {u v : R} (hc : ∃ a b : R, u * a + v * b = 1) :
    Localization.Away u →ₐ[R] LinCurve u v where
  toRingHom := IsLocalization.Away.lift u (image_isUnit hc)
  commutes' r := IsLocalization.Away.lift_eq u (image_isUnit hc) r

/-- The actual linear relation uz=v inverts u whenever u and v generate the unit ideal. -/
def linearEquationLocalization {u v : R} (hc : ∃ a b : R, u * a + v * b = 1) :
    LinCurve u v ≃ₐ[R] Localization.Away u := by
  refine AlgEquiv.ofAlgHom (toLocalization u v) (fromLocalization hc) ?_ ?_
  · apply IsLocalization.algHom_ext (Submonoid.powers u)
    apply AlgHom.ext
    intro a
    simp only [AlgHom.comp_apply, Algebra.algHom_apply, AlgHom.commutes, AlgHom.id_apply]
  · apply AdjoinRoot.algHom_ext
    let i := algebraMap R (LinCurve u v)
    let z := AdjoinRoot.root (linearEquation u v)
    let b := fromLocalization hc
    have hInv : i u * b (IsLocalization.Away.invSelf u) = 1 := by
      have h := congrArg (fun x : Localization.Away u => b x)
        (IsLocalization.Away.mul_invSelf (S := Localization.Away u) u)
      simpa only [map_mul, map_one, AlgHom.commutes] using h
    have hroot : toLocalization u v z = localizedRoot u v :=
      AdjoinRoot.liftAlgHom_root _ _ _ _
    change b (toLocalization u v z) = z
    rw [hroot]
    calc
      _ = b (IsLocalization.Away.invSelf u) * i v := by
        unfold localizedRoot
        rw [map_mul, b.commutes]
      _ = b (IsLocalization.Away.invSelf u) * (i u * z) := by
        rw [root_relation]
      _ = z := by rw [← mul_assoc, mul_comm _ (i u), hInv, one_mul]

variable (K : Type*) [CommRing K]

/-- In the chart Y=1 the printed nodal equation is z=x²(x+z). -/
theorem nodalYEquation (K : Type*) [CommRing K] :
    linearEquation ((1 : K[X]) - X ^ 2) ((X : K[X]) ^ 3) =
      (X : K[X][X]) - C ((X : K[X]) ^ 2) * (C (X : K[X]) + X) := by
  simp only [linearEquation, map_sub, map_pow, map_one]
  ring

/-- The coordinate algebra of the Y=1 chart is K[x,(1−x²)⁻¹]. -/
def nodalYChartEquiv :
    LinCurve ((1 : K[X]) - X ^ 2) ((X : K[X]) ^ 3) ≃ₐ[K[X]]
      Localization.Away ((1 : K[X]) - X ^ 2) :=
  linearEquationLocalization ⟨1 + (X : K[X]) ^ 2, X, by ring⟩

end
end ManuscriptAudit.NodalYChartAlgebra

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalYChartAlgebra.linearEquationLocalization,
      ``ManuscriptAudit.NodalYChartAlgebra.nodalYEquation,
      ``ManuscriptAudit.NodalYChartAlgebra.nodalYChartEquiv] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
