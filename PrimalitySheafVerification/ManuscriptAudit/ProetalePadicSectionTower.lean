import Lean.Util.CollectAxioms
import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology
import Mathlib.Topology.ContinuousMap.Algebra
import PrimalitySheafVerification.ManuscriptAudit.CyclicPowerInverseLimit
import PrimalitySheafVerification.ManuscriptAudit.PadicResidueHomeomorphism

/-! Sections of the actual pro-étale adic sheaf are compatible continuous residue sections. -/

namespace ManuscriptAudit.ProetalePadicSectionTower

open AlgebraicGeometry CategoryTheory Opposite Topology
open CyclicPowerInverseLimit (compatibleTuples)
open PadicResidueSystems (systems reduction compatible_of_successors)
open PadicResidueHomeomorphism (homeomorphism homeomorphism_apply reduction_continuous)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

variable (ℓ : ℕ) [Fact ℓ.Prime]
variable (T : Type u) [TopologicalSpace T]

/-- Apply the native residue reduction to a continuous finite-level section. -/
def sectionTransition (n : ℕ) : C(T, ZMod (ℓ ^ (n + 1))) →+ C(T, ZMod (ℓ ^ n)) where
  toFun f := ⟨fun x ↦ reduction ℓ (Nat.le_succ n) (f x),
    continuous_of_discreteTopology.comp f.continuous⟩
  map_zero' := by
    apply ContinuousMap.ext
    intro x
    exact map_zero _
  map_add' f g := by
    apply ContinuousMap.ext
    intro x
    exact map_add _ _ _

/-- The actual compatible tuple group of continuous finite-level sections. -/
abbrev compatibleSections :=
  compatibleTuples (fun n ↦ C(T, ZMod (ℓ ^ n))) (sectionTransition ℓ T)

/-- Each continuous p-adic-valued section gives its actual compatible continuous reductions. -/
def sectionReductions (f : C(T, ℤ_[ℓ])) : compatibleSections ℓ T :=
  ⟨fun n ↦ ⟨fun x ↦ PadicInt.toZModPow n (f x), (reduction_continuous ℓ n).comp f.continuous⟩,
    fun n ↦ by
      apply ContinuousMap.ext
      intro x
      exact RingHom.congr_fun
        (PadicInt.zmod_cast_comp_toZModPow n (n + 1) (Nat.le_succ n)) (f x)⟩

private def pointResidues (f : compatibleSections ℓ T) (x : T) : systems ℓ :=
  ⟨fun n ↦ f.val n x, compatible_of_successors ℓ _ (fun n ↦
    congrArg (fun g : C(T, ZMod (ℓ ^ n)) ↦ g x) (f.property n))⟩

private theorem continuous_pointResidues (f : compatibleSections ℓ T) :
    Continuous (pointResidues ℓ T f) := by
  apply IsEmbedding.subtypeVal.continuous_iff.mpr
  exact continuous_pi (fun n ↦ (f.val n).continuous)

/-- Continuous p-adic sections identify additively with their actual coherent residues. -/
def continuousSectionsEquiv : C(T, ℤ_[ℓ]) ≃+ compatibleSections ℓ T where
  toFun := sectionReductions ℓ T
  invFun f := ⟨fun x ↦ (homeomorphism ℓ).symm (pointResidues ℓ T f x),
    (homeomorphism ℓ).symm.continuous.comp (continuous_pointResidues ℓ T f)⟩
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    exact (homeomorphism ℓ).symm_apply_apply (f x)
  right_inv f := by
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro x
    change PadicInt.toZModPow n ((homeomorphism ℓ).symm (pointResidues ℓ T f x)) = f.val n x
    rw [← homeomorphism_apply, Homeomorph.apply_symm_apply] <;> rfl
  map_add' f g := by
    apply Subtype.ext
    funext n
    apply ContinuousMap.ext
    intro x
    exact map_add (PadicInt.toZModPow n) (f x) (g x)

variable {T}

/-- At each actual pro-étale object, the native p-adic sheaf has the coherent continuous residue sections. -/
def sheafSectionsEquiv (X : Scheme.{u}) (W : X.ProEt) :
    (X.ellAdicSheaf ℓ).obj.obj (op W) ≃+ compatibleSections ℓ W.left :=
  continuousSectionsEquiv ℓ W.left

/-- The actual evaluation of the comparison at any residue level and geometric scheme point. -/
theorem sheafSectionsEquiv_apply (X : Scheme.{u}) (W : X.ProEt)
    (f : (X.ellAdicSheaf ℓ).obj.obj (op W)) (n : ℕ) (x : W.left) :
    (sheafSectionsEquiv ℓ X W f).val n x = PadicInt.toZModPow n (f x) :=
  rfl

/-- The coherent residues commute with restriction along every actual pro-étale chart arrow. -/
theorem sheafSectionsEquiv_restrict (X : Scheme.{u}) {V W : X.ProEt} (g : V ⟶ W)
    (f : (X.ellAdicSheaf ℓ).obj.obj (op W)) (n : ℕ) (x : V.left) :
    (sheafSectionsEquiv ℓ X V ((X.ellAdicSheaf ℓ).obj.map g.op f)).val n x =
      (sheafSectionsEquiv ℓ X W f).val n (g.left x) :=
  rfl

end
end ManuscriptAudit.ProetalePadicSectionTower

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetalePadicSectionTower.sectionTransition,
      ``ManuscriptAudit.ProetalePadicSectionTower.continuousSectionsEquiv,
      ``ManuscriptAudit.ProetalePadicSectionTower.sheafSectionsEquiv,
      ``ManuscriptAudit.ProetalePadicSectionTower.sheafSectionsEquiv_apply,
      ``ManuscriptAudit.ProetalePadicSectionTower.sheafSectionsEquiv_restrict] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
