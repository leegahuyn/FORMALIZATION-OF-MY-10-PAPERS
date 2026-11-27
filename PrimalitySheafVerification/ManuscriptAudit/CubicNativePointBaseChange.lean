import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CubicFrobeniusSecantPoints

/-! Native base extension of actual centered cubic points commutes with relative Frobenius. -/

namespace ManuscriptAudit.CubicNativePointBaseChange

open WeierstrassCurve CubicThreeTorsionOrdinate CubicNonsplitFrobeniusTrace
open CubicNonsplitThreeAdicTrace CubicFrobeniusSecantPoints

noncomputable section

variable {K L M : Type*} [Field K] [Field L] [Field M]
  [DecidableEq L] [DecidableEq M] [Algebra K L] [Algebra K M]

private def pointTransport (F : Type*) [Field F] [DecidableEq F]
    {C D : WeierstrassCurve.Affine F} (h : C = D) : C.Point ≃+ D.Point := by
  subst D
  exact AddEquiv.refl _

/-- The actual point-group map along an extension of fields. -/
def pointsMap (A : K) (f : L →ₐ[K] M) :
    GeometricPoints K L A →+ GeometricPoints K M A :=
  let eL := pointTransport L (centered_baseChange K L A)
  let eM := pointTransport M (centered_baseChange K M A)
  eM.toAddMonoidHom.comp ((Affine.Point.map (W' := Curve A) f).comp eL.symm.toAddMonoidHom)

theorem pointsMap_injective (A : K) (f : L →ₐ[K] M) : Function.Injective (pointsMap A f) := by
  let eL := pointTransport L (centered_baseChange K L A)
  let eM := pointTransport M (centered_baseChange K M A)
  exact eM.injective.comp ((Affine.Point.map_injective (W' := Curve A) f).comp eL.symm.injective)

private theorem pointsMap_some_aux (A : K) (f : L →ₐ[K] M)
    (C : WeierstrassCurve.Affine L) (D : WeierstrassCurve.Affine M)
    (hL : (Curve A).baseChange L = C) (hM : (Curve A).baseChange M = D)
    (x y : L) (h : C.Nonsingular x y) :
    let eL := pointTransport L hL
    let eM := pointTransport M hM
    ∃ h' : D.Nonsingular (f x) (f y),
      (eM.toAddMonoidHom.comp ((Affine.Point.map (W' := Curve A) f).comp eL.symm.toAddMonoidHom))
        (Affine.Point.some x y h) = Affine.Point.some (f x) (f y) h' := by
  subst C
  subst D
  exact ⟨_, rfl⟩

theorem pointsMap_some (A : K) (f : L →ₐ[K] M) (x y : L)
    (h : (Curve (algebraMap K L A)).Nonsingular x y) :
    ∃ h' : (Curve (algebraMap K M A)).Nonsingular (f x) (f y),
      pointsMap A f (Affine.Point.some x y h) = Affine.Point.some (f x) (f y) h' :=
  pointsMap_some_aux A f _ _ (centered_baseChange K L A) (centered_baseChange K M A) x y h

variable [Fintype K]

/-- The base extension commutes with actual q-power Frobenius as additive maps. -/
theorem map_arithmeticFrobenius (A : K) (f : L →ₐ[K] M) (P : GeometricPoints K L A) :
    pointsMap A f (arithmeticPointFrobenius K L A P) =
      arithmeticPointFrobenius K M A (pointsMap A f P) := by
  cases P with
  | zero =>
    change pointsMap A f (arithmeticPointFrobenius K L A 0) =
      arithmeticPointFrobenius K M A (pointsMap A f 0)
    simp only [map_zero]
  | some x y h =>
    obtain ⟨hFL, eFL⟩ := actual_frobenius_some K L A x y h
    obtain ⟨hM, eM⟩ := pointsMap_some A f x y h
    obtain ⟨hFM, eFM⟩ := actual_frobenius_some K M A (f x) (f y) hM
    obtain ⟨hLF, eLF⟩ := pointsMap_some A f _ _ hFL
    rw [eFL, eM, eFM, eLF, Affine.Point.some.injEq]
    exact ⟨map_pow f x _, map_pow f y _⟩

end

end ManuscriptAudit.CubicNativePointBaseChange

open Lean Elab Command in
run_cmd do
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for name in #[
      ``ManuscriptAudit.CubicNativePointBaseChange.pointsMap_injective,
      ``ManuscriptAudit.CubicNativePointBaseChange.pointsMap_some,
      ``ManuscriptAudit.CubicNativePointBaseChange.map_arithmeticFrobenius] do
    let ax ← collectAxioms name
    unless ax.all (allowed.contains ·) do
      throwError m!"{name} unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
