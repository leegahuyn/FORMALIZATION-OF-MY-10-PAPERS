import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetalePadicSectionTower

/-! The genuine pro-étale finite residue sheaves and reductions from the adic sheaf. -/

namespace ManuscriptAudit.ProetaleResidueSheaves

open AlgebraicGeometry CategoryTheory Opposite
open PadicResidueSystems (reduction)
open PadicResidueHomeomorphism (reduction_continuous)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}

variable (X : Scheme.{0})

/-- The native pro-étale sheaf of continuous maps into an additive topological group. -/
def continuousCoefficients (M : Type) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M] :
    Sheaf (Scheme.ProEt.topology X) A :=
  ((Scheme.ProEt.forget X ⋙ Over.forget X).sheafPushforwardContinuous _ _ Scheme.proetaleTopology).obj
    ⟨continuousMapPresheafAb M, .of_le Scheme.proetaleTopology_le_fpqcTopology
      (isSheaf_fpqcTopology_continuousMapPresheafAb M)⟩

variable {M N : Type} [AddCommGroup M] [AddCommGroup N] [TopologicalSpace M] [TopologicalSpace N]
    [IsTopologicalAddGroup M] [IsTopologicalAddGroup N]

/-- A continuous additive arrow acts on the native pro-étale sections by postcomposition. -/
def coefficientMap (f : M →+ N) (hf : Continuous f) :
    continuousCoefficients X M ⟶ continuousCoefficients X N where
  hom :=
    { app := fun W ↦ AddCommGrpCat.ofHom
        { toFun := fun g ↦ ⟨fun x ↦ f (g x), hf.comp g.continuous⟩
          map_zero' := by
            apply ContinuousMap.ext
            intro x
            exact f.map_zero
          map_add' := fun g h ↦ by
            apply ContinuousMap.ext
            intro x
            exact f.map_add (g x) (h x) }
      naturality := fun U V g ↦ by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro a
        apply ContinuousMap.ext
        intro x
        rfl }

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]

/-- Finite residue sheaves on the actual pro-étale site use the discrete finite cyclic coefficient. -/
abbrev residueSheaf (n : ℕ) := continuousCoefficients X (ZMod (ℓ ^ n))

/-- Native finite reduction is a morphism of the actual sheaves. -/
def residueTransition (n : ℕ) : residueSheaf X ℓ (n + 1) ⟶ residueSheaf X ℓ n :=
  coefficientMap X (reduction ℓ (Nat.le_succ n)).toAddMonoidHom continuous_of_discreteTopology

/-- The actual integral adic sheaf reduces to each discrete finite residue sheaf. -/
def residueReduction (n : ℕ) : X.ellAdicSheaf ℓ ⟶ residueSheaf X ℓ n :=
  coefficientMap X (PadicInt.toZModPow n).toAddMonoidHom (reduction_continuous ℓ n)

theorem residueReduction_comp (n : ℕ) :
    residueReduction X ℓ (n + 1) ≫ residueTransition X ℓ n = residueReduction X ℓ n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro f
  apply ContinuousMap.ext
  intro x
  exact RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n))
    ((show C(W.unop.left, ℤ_[ℓ]) from f) x)

end
end ManuscriptAudit.ProetaleResidueSheaves

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleResidueSheaves.coefficientMap,
      ``ManuscriptAudit.ProetaleResidueSheaves.residueTransition,
      ``ManuscriptAudit.ProetaleResidueSheaves.residueReduction,
      ``ManuscriptAudit.ProetaleResidueSheaves.residueReduction_comp] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
