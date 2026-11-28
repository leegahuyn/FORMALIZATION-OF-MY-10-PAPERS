import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveClosure

/-! The proper Weierstrass closure genuinely adds a point beyond its affine chart. -/

namespace ManuscriptAudit.WeierstrassProjectiveInfinityExists

open AlgebraicGeometry CategoryTheory Polynomial WeierstrassCurve.Affine
open WeierstrassProjectiveClosure

universe u

noncomputable section

variable {K : Type u} [Field K] (W : WeierstrassCurve.Affine K)

private theorem not_finite_coordinate : ¬ Module.Finite K W.CoordinateRing := by
  intro h
  letI : Module.Finite K W.CoordinateRing := h
  let f : K[X] →ₗ[K] W.CoordinateRing :=
    (Algebra.linearMap K[X] W.CoordinateRing).restrictScalars K
  have hInjective : Function.Injective f :=
    FaithfulSMul.algebraMap_injective K[X] W.CoordinateRing
  letI : Module.Finite K K[X] := Module.Finite.of_injective f hInjective
  have hIntegral : IsIntegral K (Polynomial.X : K[X]) := Algebra.IsIntegral.isIntegral _
  obtain ⟨p, hp, hRoot⟩ := hIntegral
  have hZero : p = 0 := by
    simpa only [Polynomial.aeval_X_left_apply] using hRoot
  exact hp.ne_zero hZero

/-- The literal affine Weierstrass coordinate spectrum is not proper over its field. -/
theorem affine_not_proper :
    ¬ IsProper (Spec.map (CommRingCat.ofHom (algebraMap K W.CoordinateRing))) := by
  intro h
  let f := Spec.map (CommRingCat.ofHom (algebraMap K W.CoordinateRing))
  have hf : IsFinite f := IsFinite.iff_isProper_and_isAffineHom.mpr ⟨h, inferInstance⟩
  have hRing : (algebraMap K W.CoordinateRing).Finite :=
    (HasRingHomProperty.Spec_iff (P := @IsFinite)).mp hf
  exact not_finite_coordinate W (by simpa only [RingHom.finite_algebraMap] using hRing)

/-- The actual proper closure has a boundary point outside the given affine immersion. -/
theorem exists_boundary :
    ∃ x : projectiveScheme W, x ∉ Set.range (WeierstrassProjectiveClosure.affineOpen W) := by
  classical
  by_contra! h
  have hRange : (WeierstrassProjectiveClosure.affineOpen W).opensRange = ⊤ :=
    TopologicalSpace.Opens.ext (Set.eq_univ_of_forall h)
  letI : IsIso (WeierstrassProjectiveClosure.affineOpen W) :=
    isIso_of_isOpenImmersion_of_opensRange_eq_top _ hRange
  letI : IsProper (toBase W) := toBase_isProper W
  have hComp : IsProper (WeierstrassProjectiveClosure.affineOpen W ≫ toBase W) := inferInstance
  rw [affineOpen_toBase] at hComp
  exact affine_not_proper W hComp

end

end ManuscriptAudit.WeierstrassProjectiveInfinityExists

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassProjectiveInfinityExists.affine_not_proper,
      ``ManuscriptAudit.WeierstrassProjectiveInfinityExists.exists_boundary] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
