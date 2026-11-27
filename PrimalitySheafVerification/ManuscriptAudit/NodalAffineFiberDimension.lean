import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Ideal.GoingUp
import PrimalitySheafVerification.ManuscriptAudit.ArithmeticLineModel
import PrimalitySheafVerification.ManuscriptAudit.NodalAffineOrigin

/-! The actual affine nodal chart is a one-dimensional scheme. This
uses its monic presentation for the upper bound and the actual
singular closed point for a strict prime chain. -/

namespace ManuscriptAudit.NodalAffineFiberDimension

open AlgebraicGeometry Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev A := NodalConductor.coordinates K

private theorem chart_ring_dim_le_one : ringKrullDim (A K) ≤ 1 := by
  let p := NodalAffinePresentation.equation K
  let B := AdjoinRoot p
  have hM : p.Monic := Polynomial.monic_X_pow_sub_C _ (n := 2) (by decide)
  letI : Module.Finite (Polynomial K) B := hM.finite_adjoinRoot
  letI : Algebra.IsIntegral (Polynomial K) B := Algebra.IsIntegral.of_finite _ _
  have hS : StrictMono (PrimeSpectrum.comap (algebraMap (Polynomial K) B)) := by
    intro P Q h
    change Ideal.comap (algebraMap (Polynomial K) B) P.asIdeal <
      Ideal.comap (algebraMap (Polynomial K) B) Q.asIdeal
    letI := P.isPrime
    exact Ideal.IsIntegral.comap_lt_comap h
  have hD : ringKrullDim B ≤ ringKrullDim (Polynomial K) :=
    Order.krullDim_le_of_strictMono _ hS
  have hE : ringKrullDim B = ringKrullDim (A K) :=
    ringKrullDim_eq_of_ringEquiv (NodalAffinePresentation.coordinateEquiv K).toRingEquiv
  rw [← hE, ← ArithmeticLineModel.fiber_coordinate_dimension K]
  exact hD

private theorem nodeX_ne_zero : NodalAffinePresentation.nodeX K ≠ 0 := by
  intro h
  have hx : NodalConductor.x K = 0 := congrArg Subtype.val h
  have h₂ := congrArg (fun p : Polynomial K => p.coeff 2) hx
  simp [NodalConductor.x] at h₂

/-- The native affine nodal coordinate ring has Krull dimension one. -/
theorem chart_ring_dimension : ringKrullDim (A K) = 1 := by
  apply le_antisymm (chart_ring_dim_le_one K)
  apply Order.one_le_krullDim_iff.mpr
  refine ⟨(⊥ : PrimeSpectrum (A K)), NodalAffineOrigin.originPoint K, lt_of_le_of_ne bot_le ?_⟩
  intro h
  have hx := (NodalAffineOrigin.prime_eq_origin_iff_x_mem K
    (NodalAffineOrigin.originPoint K)).mp rfl
  rw [← h] at hx
  have hx0 : NodalAffinePresentation.nodeX K ∈ (⊥ : Ideal (A K)) := hx
  exact nodeX_ne_zero K (Ideal.mem_bot.mp hx0)

end
end ManuscriptAudit.NodalAffineFiberDimension

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalAffineFiberDimension.chart_ring_dimension
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
