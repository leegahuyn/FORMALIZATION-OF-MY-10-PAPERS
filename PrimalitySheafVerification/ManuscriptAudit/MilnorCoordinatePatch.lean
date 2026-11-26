import Lean.Util.CollectAxioms
import Mathlib.Algebra.Module.Submodule.EqLocus
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Prod

/-!
# Fixed-coordinate module patching

The two coordinate vectors form a submodule when their images in the
common ring agree after application of the transition matrix. When that
matrix lifts to an invertible matrix on the first side, a change of
coordinates reduces the condition to equality of the images.
-/

namespace ManuscriptAudit.MilnorCoordinatePatch

open Matrix

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
variable [Algebra A B] [Algebra A C] [Algebra A D]
variable {n : Type v} [Fintype n]
variable (q : B →ₐ[A] D) (s : C →ₐ[A] D)

/-- The submodule of pairs of coordinate vectors satisfying the transition equation. -/
def patch (U : Matrix n n D) : Submodule A ((n → B) × (n → C)) :=
  LinearMap.eqLocus
    ((q.toLinearMap.compLeft n).comp (LinearMap.fst A (n → B) (n → C)))
    ((U.mulVecLin.restrictScalars A).comp
      ((s.toLinearMap.compLeft n).comp (LinearMap.snd A (n → B) (n → C))))

theorem mem_patch_iff (U : Matrix n n D) (x : (n → B) × (n → C)) :
    x ∈ patch q s U ↔ q ∘ x.1 = U *ᵥ (s ∘ x.2) :=
  Iff.rfl

variable [DecidableEq n]

theorem mem_patch_one_iff (x : (n → B) × (n → C)) :
    x ∈ patch q s (1 : Matrix n n D) ↔ q ∘ x.1 = s ∘ x.2 := by
  rw [mem_patch_iff, one_mulVec]

variable (A C) in
private def changeCoordinates (V : GL n B) : ((n → B) × (n → C)) ≃ₗ[A] (n → B) × (n → C) :=
  ((Matrix.toLin'OfInv V.val_inv V.inv_val).restrictScalars A).prodCongr
    (LinearEquiv.refl A (n → C))

private theorem changeCoordinates_mem_iff (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U) (x : (n → B) × (n → C)) :
    changeCoordinates A C V x ∈ patch q s (1 : Matrix n n D) ↔ x ∈ patch q s U.val := by
  rw [mem_patch_one_iff, mem_patch_iff]
  change q ∘ (V.inv *ᵥ x.1) = s ∘ x.2 ↔ q ∘ x.1 = U.val *ᵥ (s ∘ x.2)
  have hInv : V.inv.map q.toRingHom = U.inv := congrArg Units.inv hV
  have hMap : q ∘ (V.inv *ᵥ x.1) = V.inv.map q.toRingHom *ᵥ (q ∘ x.1) :=
    funext fun i => RingHom.map_mulVec q.toRingHom V.inv x.1 i
  rw [hMap, hInv]
  constructor
  · intro h
    have h' := congrArg (fun y : n → D => U.val *ᵥ y) h
    rwa [mulVec_mulVec, U.val_inv, one_mulVec] at h'
  · intro h
    rw [h, mulVec_mulVec, U.inv_val, one_mulVec]

/-- A lift of the transition matrix identifies its patch with the patch for the identity. -/
def equivOfLift (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U) :
    patch q s U.val ≃ₗ[A] patch q s (1 : Matrix n n D) := by
  let e := changeCoordinates A C V
  refine e.ofSubmodules _ _ ?_
  apply Submodule.ext
  intro x
  rw [Submodule.mem_map_equiv, ← changeCoordinates_mem_iff q s U V hV (e.symm x)]
  exact Iff.of_eq (congrArg (fun y => y ∈ patch q s (1 : Matrix n n D)) (e.apply_symm_apply x))

/-- The forward equivalence acts on the first coordinate by the inverse lift. -/
theorem equivOfLift_apply_coe (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U) (x : patch q s U.val) :
    ↑(equivOfLift q s U V hV x) = (V.inv *ᵥ x.val.1, x.val.2) :=
  rfl

/-- The inverse equivalence acts on the first coordinate by the lift. -/
theorem equivOfLift_symm_apply_coe (U : GL n D) (V : GL n B)
    (hV : GeneralLinearGroup.map q.toRingHom V = U) (x : patch q s (1 : Matrix n n D)) :
    ↑((equivOfLift q s U V hV).symm x) = (V.val *ᵥ x.val.1, x.val.2) :=
  rfl

end ManuscriptAudit.MilnorCoordinatePatch

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.MilnorCoordinatePatch.mem_patch_iff,
      ``ManuscriptAudit.MilnorCoordinatePatch.equivOfLift,
      ``ManuscriptAudit.MilnorCoordinatePatch.equivOfLift_apply_coe,
      ``ManuscriptAudit.MilnorCoordinatePatch.equivOfLift_symm_apply_coe] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
