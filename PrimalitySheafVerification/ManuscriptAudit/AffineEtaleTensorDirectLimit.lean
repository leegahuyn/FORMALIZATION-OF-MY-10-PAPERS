import Lean.Util.CollectAxioms
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.CategoryTheory.Functor.OfSequence
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorStages

/-! The countable tensor stages have their genuine directed limit, and
faithfully flat transition maps inject each stage into the limit algebra. -/

namespace ManuscriptAudit.AffineEtaleTensorDirectLimit

open CategoryTheory
open AffineEtaleTensorStages (stage step step_injective)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u

variable {R : Type u} [CommRing R] (B : ℕ → CommAlgCat.{u} R)

abbrev Stage (n : ℕ) := ↥(stage B n)

private abbrev diagram : ℕ ⥤ CommAlgCat.{u} R := Functor.ofSequence (step B)

def transition (i j : ℕ) (h : i ≤ j) : Stage B i →ₐ[R] Stage B j :=
  ((diagram B).map (homOfLE h)).hom

instance directedStages : DirectedSystem (Stage B) (fun i j h ↦ transition B i j h) where
  map_self := by
    intro i x
    have h : homOfLE (Nat.le_refl i) = 𝟙 i := Subsingleton.elim _ _
    change ((diagram B).map (homOfLE (Nat.le_refl i))).hom x = x
    rw [h, Functor.map_id]
    rfl
  map_map := by
    intro k j i hij hjk x
    have h : homOfLE hij ≫ homOfLE hjk = homOfLE (hij.trans hjk) := Subsingleton.elim _ _
    have heq := congrArg (fun φ : i ⟶ k ↦ ((diagram B).map φ).hom x) h
    simpa only [Functor.map_comp, CommAlgCat.hom_comp, AlgHom.comp_apply, transition] using heq

theorem transition_injective (hFlat : ∀ n, Module.FaithfullyFlat R (B n))
    {i j : ℕ} (hij : i ≤ j) : Function.Injective (transition B i j hij) := by
  induction hij using Nat.leRec with
  | refl =>
    intro x y h
    simpa only [DirectedSystem.map_self] using h
  | @le_succ_of_le j hj ih =>
    have h : homOfLE (by omega : i ≤ j + 1) = homOfLE hj ≫ homOfLE (Nat.le_add_right j 1) :=
      Subsingleton.elim _ _
    unfold transition
    rw [h, Functor.map_comp, Functor.ofSequence_map_homOfLE_succ, CommAlgCat.hom_comp]
    exact (step_injective B hFlat j).comp ih

abbrev Tower := DirectLimit (Stage B) (transition B)

/-- The actual maps from each finite tensor stage into the countable tensor algebra. -/
def stageMap (n : ℕ) : Stage B n →ₐ[R] Tower B :=
  Algebra.DirectLimit.of (Stage B) (transition B) n

theorem stageMap_transition {i j : ℕ} (h : i ≤ j) (x : Stage B i) :
    stageMap B j (transition B i j h x) = stageMap B i x :=
  Algebra.DirectLimit.of_f (G := Stage B) (f := transition B) h x

theorem stageMap_injective (hFlat : ∀ n, Module.FaithfullyFlat R (B n)) (n : ℕ) :
    Function.Injective (stageMap B n) := by
  intro x y h
  change (⟦⟨n, x⟩⟧ : Tower B) = ⟦⟨n, y⟩⟧ at h
  obtain ⟨m, hm, _, he⟩ := Quotient.exact h
  exact transition_injective B hFlat hm he

theorem exists_stage (x : Tower B) :
    ∃ n, ∃ z : Stage B n, stageMap B n z = x := by
  obtain ⟨n, z, hz⟩ := DirectLimit.exists_eq_mk x
  exact ⟨n, z, hz.symm⟩

end

end ManuscriptAudit.AffineEtaleTensorDirectLimit

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleTensorDirectLimit.stageMap_transition,
      ``ManuscriptAudit.AffineEtaleTensorDirectLimit.stageMap_injective,
      ``ManuscriptAudit.AffineEtaleTensorDirectLimit.exists_stage] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
