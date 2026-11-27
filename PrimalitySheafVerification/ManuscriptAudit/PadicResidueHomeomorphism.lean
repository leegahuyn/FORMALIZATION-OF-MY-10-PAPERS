import Lean.Util.CollectAxioms
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.MetricSpace.Ultra.Basic
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueSystems

/-! The actual p-adic topology is the residue-tower topology. -/

namespace ManuscriptAudit.PadicResidueHomeomorphism

open Filter Topology
open PadicResidueSystems (systems padicRingEquiv evaluate_padicRingEquiv)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- Each finite reduction has an open kernel for the true p-adic topology. -/
theorem reduction_kernel_open (n : ℕ) :
    IsOpen {x : ℤ_[p] | PadicInt.toZModPow n x = 0} := by
  let t : ℝ := (p : ℝ) ^ (-(n : ℤ))
  have h : {x : ℤ_[p] | PadicInt.toZModPow n x = 0} = Metric.closedBall 0 t := by
    ext x
    change PadicInt.toZModPow n x = 0 ↔ dist x 0 ≤ t
    rw [dist_eq_norm, sub_zero]
    change PadicInt.toZModPow n x = 0 ↔ ‖x‖ ≤ (p : ℝ) ^ (-(n : ℤ))
    rw [PadicInt.norm_le_pow_iff_mem_span_pow, ← PadicInt.ker_toZModPow, RingHom.mem_ker]
  rw [h]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  exact IsUltrametricDist.isOpen_closedBall 0 (zpow_pos hp _).ne'

/-- Every actual p-adic reduction to the discrete finite ring is continuous. -/
theorem reduction_continuous (n : ℕ) : Continuous (PadicInt.toZModPow n : ℤ_[p] → ZMod (p ^ n)) := by
  apply continuous_of_tendsto_nhds_zero (PadicInt.toZModPow n : ℤ_[p] →+* ZMod (p ^ n)).toAddMonoidHom
  rw [nhds_discrete]
  exact tendsto_pure.mpr ((reduction_kernel_open p n).mem_nhds (map_zero _))

/-- The native residue ring equivalence is a homeomorphism for the product-subspace topology. -/
def homeomorphism : ℤ_[p] ≃ₜ systems p := by
  let e := (padicRingEquiv p).toEquiv
  have h : Continuous e := by
    apply IsEmbedding.subtypeVal.continuous_iff.mpr
    exact continuous_pi (fun n ↦ reduction_continuous p n)
  let he := (h.isClosedEmbedding e.injective).isEmbedding
  refine ⟨e, h, he.continuous_iff.mpr ?_⟩
  have hId : e ∘ e.symm = id := funext e.apply_symm_apply
  rw [hId]
  exact continuous_id

theorem homeomorphism_apply (x : ℤ_[p]) (n : ℕ) :
    ((homeomorphism p x).val n) = PadicInt.toZModPow n x := rfl

end
end ManuscriptAudit.PadicResidueHomeomorphism

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.PadicResidueHomeomorphism.reduction_kernel_open,
      ``ManuscriptAudit.PadicResidueHomeomorphism.reduction_continuous,
      ``ManuscriptAudit.PadicResidueHomeomorphism.homeomorphism,
      ``ManuscriptAudit.PadicResidueHomeomorphism.homeomorphism_apply] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
