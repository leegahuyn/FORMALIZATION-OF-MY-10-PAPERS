import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SchemeIsoProetaleCohomologyNaturality
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHOneDetection
import PrimalitySheafVerification.ManuscriptAudit.CompatibleTowerCongruence

/-! Native adic reduction commutes with actual scheme isomorphism
transport, including the entire compatible finite residue tower. -/

namespace ManuscriptAudit.SchemeIsoNativeAdicReduction

open AlgebraicGeometry CategoryTheory
open SchemeIsoProetaleCohomology (continuousCohomologyEquiv adicCohomologyEquiv)
open SchemeIsoProetaleCohomologyNaturality (continuousCohomologyEquiv_map)
open ProetaleAdicHOneDetection (finiteCoefficient compatibleHOne reductionMap reductionMap_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (e : X ≅ Y) (ℓ : ℕ) [Fact ℓ.Prime]

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

private abbrev lift (T : Scheme.{0}) :=
  sheafCompose (Scheme.ProEt.topology T) AddCommGrpCat.uliftFunctor.{1}
private abbrev level (T : Scheme.{0}) (n : ℕ) := Sheaf.H (finiteCoefficient T ℓ n) 1
private abbrev step (T : Scheme.{0}) (n : ℕ) :=
  Sheaf.H.map ((lift T).map (ProetaleResidueSheaves.residueTransition T ℓ n)) 1
private abbrev residueEquiv (n : ℕ) : level ℓ X n ≃+ level ℓ Y n :=
  continuousCohomologyEquiv e (ZMod (ℓ ^ n)) 1

private theorem residue_natural (n : ℕ) (x : level ℓ X (n + 1)) :
    residueEquiv e ℓ n (step ℓ X n x) = step ℓ Y n (residueEquiv e ℓ (n + 1) x) :=
  continuousCohomologyEquiv_map e
    (PadicResidueSystems.reduction ℓ (Nat.le_succ n)).toAddMonoidHom
    continuous_of_discreteTopology 1 x

/-- The actual finite classes, with their actual transition maps. -/
def compatibleEquiv : compatibleHOne X ℓ ≃+ compatibleHOne Y ℓ :=
  CompatibleTowerCongruence.compatibleEquiv (level ℓ X) (level ℓ Y)
    (step ℓ X) (step ℓ Y) (residueEquiv e ℓ) (residue_natural e ℓ)

/-- The native integral comparison commutes with the genuine finite reductions. -/
theorem reduction_natural (a : X.EllAdicCohomology ℓ 1) :
    compatibleEquiv e ℓ (reductionMap X ℓ a) =
      reductionMap Y ℓ (adicCohomologyEquiv e ℓ 1 a) := by
  apply Subtype.ext
  funext n
  exact continuousCohomologyEquiv_map e (PadicInt.toZModPow n).toAddMonoidHom
    (PadicResidueHomeomorphism.reduction_continuous ℓ n) 1 a

theorem reduction_surjective_of_iso (hY : Function.Surjective (reductionMap Y ℓ)) :
    Function.Surjective (reductionMap X ℓ) := by
  intro x
  let E := adicCohomologyEquiv e ℓ 1
  obtain ⟨y, hy⟩ := hY (compatibleEquiv e ℓ x)
  refine ⟨E.symm y, (compatibleEquiv e ℓ).injective ?_⟩
  calc
    _ = reductionMap Y ℓ (E (E.symm y)) := reduction_natural e ℓ (E.symm y)
    _ = reductionMap Y ℓ y := congrArg (reductionMap Y ℓ) (E.apply_symm_apply y)
    _ = _ := hy

def reductionEquivOfIso (hY : Function.Surjective (reductionMap Y ℓ)) :
    X.EllAdicCohomology ℓ 1 ≃+ compatibleHOne X ℓ :=
  AddEquiv.ofBijective (reductionMap X ℓ)
    ⟨reductionMap_injective X ℓ, reduction_surjective_of_iso e ℓ hY⟩

end
end ManuscriptAudit.SchemeIsoNativeAdicReduction

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.SchemeIsoNativeAdicReduction.compatibleEquiv,
      ``ManuscriptAudit.SchemeIsoNativeAdicReduction.reduction_natural,
      ``ManuscriptAudit.SchemeIsoNativeAdicReduction.reduction_surjective_of_iso,
      ``ManuscriptAudit.SchemeIsoNativeAdicReduction.reductionEquivOfIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
