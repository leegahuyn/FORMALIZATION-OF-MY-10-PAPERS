import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ThetaHyperbolicTile

/-! Finite native translates of the modular tile cover the level-two quotient. -/

namespace ManuscriptAudit.ThetaLevelTwoTiles

open Set MeasureTheory Matrix
open CompactModularCore LiteralCuspTruncation
open ThetaProfileGenerators ThetaGammaTwoMetric ThetaHyperbolicTile
open scoped MatrixGroups UpperHalfPlane Pointwise

noncomputable section

theorem thetaDensity_integrableOn_translate (g : SL(2, ℤ)) :
    IntegrableOn (thetaDensity jacobiTheta) (g • ModularGroup.fd) (volume : Measure ℍ) := by
  have hp (γ : SL(2, ℤ)) :
      MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
    change MeasurePreserving (fun z : ℍ => (γ : GL (Fin 2) ℝ) • z) volume volume
    exact measurePreserving_smul _ _
  let e : MeasurableEquiv ℍ ℍ :=
    ⟨MulAction.toPerm g, (hp g).measurable, (hp g⁻¹).measurable⟩
  have he : MeasurePreserving e volume volume := hp g
  have hC : (fun z : ℍ => thetaDensity jacobiTheta (g • z)) =
      profileDensity (direction g⁻¹ (![1, 1] : Direction)) := by
    funext z
    simpa only [profileDensity, profile_11] using
      full_modular_density_covariance g (![1, 1] : Direction) z
  have hI : IntegrableOn (fun z : ℍ => thetaDensity jacobiTheta (g • z))
      ModularGroup.fd (volume : Measure ℍ) := by
    rw [hC]
    exact profileDensity_integrableOn_fd _
  exact (he.integrableOn_image e.measurableEmbedding
    (f := thetaDensity jacobiTheta) (s := ModularGroup.fd)).mpr hI

/-- A finite union of genuine modular translates meeting every level-two orbit. -/
def tileCarrier : Set ℍ := ⋃ r : Reduced, chooseLift r • ModularGroup.fd

theorem levelTwo_tiles_integrable :
    IntegrableOn (thetaDensity jacobiTheta) tileCarrier (volume : Measure ℍ) := by
  unfold tileCarrier
  apply integrableOn_iUnion_of_summable_integral_norm
  · intro r
    exact thetaDensity_integrableOn_translate (chooseLift r)
  · exact Summable.of_finite

theorem orbitPoint_image_tileCarrier : orbitPoint '' tileCarrier = univ := by
  apply eq_univ_of_forall
  intro x
  refine Quotient.inductionOn x fun z => ?_
  obtain ⟨g, hg⟩ := ModularGroup.exists_smul_mem_fd z
  let r := reduceTwo g⁻¹
  have hred : reduceTwo (chooseLift r * g) = 1 := by
    change reduceTwo (chooseLift (reduceTwo g⁻¹) * g) = 1
    rw [map_mul, reduce_chooseLift (g⁻¹), map_inv, inv_mul_cancel]
  let γ : GammaTwo := ⟨chooseLift r * g, (mem_gamma_iff_reduced_one _).mpr hred⟩
  have he : orbitPoint (γ • z) = orbitPoint z := Quotient.sound ⟨γ, rfl⟩
  refine ⟨γ • z, ?_, he⟩
  change (chooseLift r * g) • z ∈ tileCarrier
  rw [mul_smul]
  exact Set.mem_iUnion.mpr ⟨r, Set.mem_smul_set.mpr ⟨g • z, hg, rfl⟩⟩

end
end ManuscriptAudit.ThetaLevelTwoTiles

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ThetaLevelTwoTiles.thetaDensity_integrableOn_translate,
      ``ManuscriptAudit.ThetaLevelTwoTiles.levelTwo_tiles_integrable,
      ``ManuscriptAudit.ThetaLevelTwoTiles.orbitPoint_image_tileCarrier] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
