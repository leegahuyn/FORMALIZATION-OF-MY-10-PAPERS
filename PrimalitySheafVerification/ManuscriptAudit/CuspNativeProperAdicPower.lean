import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProperFinitePower
import PrimalitySheafVerification.ManuscriptAudit.ProetaleContinuousPullbackNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleDiscreteSchemePullback

/-! Finite native reductions detect the actual integral ℓ-adic action
of relative power on proper cusp cohomology. -/

namespace ManuscriptAudit.CuspNativeProperAdicPower

open AlgebraicGeometry CategoryTheory
open CuspProperCompactification (projectiveCusp)
open CuspRelativePowerMap (projectiveMap)
open CuspNativeAdicHTwoReductionDetection (reduction_injective)
open ProetaleSchemeCohomologyPullback (constant continuous)
open ProetaleContinuousPullbackNaturality (continuous_natural)
open ProetaleDiscreteSchemePullback (cohomology_pullback)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleCoefficientUniverseLift (lift)
open ProetaleResidueSheaves (residueReduction)
open ProetaleDiscreteConstant (nativeResidueIso)
open ProetaleCohomologyIso (cohomologyIso)
open PadicResidueHomeomorphism (reduction_continuous)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
  (m : ℕ) (hm : 2 ≤ m) (p : ℕ) (hp : Nat.Prime p) (hchar : CharP K p)
  (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K
private abbrev f := projectiveMap K m hm
private abbrev F (r : ℕ) := ZMod (ℓ ^ r)
private abbrev M (r : ℕ) := AddCommGrpCat.of (ULift.{1} (F ℓ r))

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

include hp hchar in
set_option maxHeartbeats 7200000 in
/-- On every actual continuous finite residue sheaf the native pullback is scalar. -/
theorem residue_scalar (r : ℕ) (x : Sheaf.H (functions (F ℓ r) (X K)) 2) :
    continuous (f K m hm) (F ℓ r) 2 x = m • x := by
  let e := cohomologyIso (nativeResidueIso (X K) ℓ r) 2
  obtain ⟨z, rfl⟩ := e.surjective x
  have h := cohomology_pullback (F ℓ r) (f K m hm) 2 z
  change continuous (f K m hm) (F ℓ r) 2 (e z) = e (constant (f K m hm) (M ℓ r) 2 z) at h
  exact h.trans ((congrArg e (CuspNativeProperFinitePower.finite_scalar K m hm p hp hchar ℓ r z)).trans
    (map_nsmul e m z))

include hp hchar in
set_option maxHeartbeats 7600000 in
/-- Actual native ℓ-adic pullback in degree two is multiplication by m. -/
theorem adic_scalar (x : (X K).EllAdicCohomology ℓ 2) :
    continuous (f K m hm) ℤ_[ℓ] 2 x = m • x := by
  apply reduction_injective K ℓ
  apply Subtype.ext
  funext r
  let q := (lift (X K)).map (residueReduction (X K) ℓ r)
  let c := (PadicInt.toZModPow r).toAddMonoidHom
  have hc : Continuous c := reduction_continuous ℓ r
  have h := continuous_natural (f K m hm) c hc 2 x
  change continuous (f K m hm) (F ℓ r) 2 (Sheaf.H.map q 2 x) =
    Sheaf.H.map q 2 (continuous (f K m hm) ℤ_[ℓ] 2 x) at h
  change Sheaf.H.map q 2 (continuous (f K m hm) ℤ_[ℓ] 2 x) =
    Sheaf.H.map q 2 (m • x)
  rw [← h, residue_scalar K m hm p hp hchar ℓ r, map_nsmul]

end
end ManuscriptAudit.CuspNativeProperAdicPower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for n in [``ManuscriptAudit.CuspNativeProperAdicPower.residue_scalar,
      ``ManuscriptAudit.CuspNativeProperAdicPower.adic_scalar] do
    let ax ← collectAxioms n
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{n} depends on unexpected axioms {ax}"
    logInfo m!"{n} uses {ax}"
