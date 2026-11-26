import Lean.Util.CollectAxioms
import Mathlib.Tactic.FinCases
import PrimalitySheafVerification.ManuscriptAudit.NodalMilnorCoefficients
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCover

/-!
# The crossed-pair algebra is the swapped Milnor patch

The transition is the identity at 1 and the transposition at -1.
The actual algebra is finite projective over the node.
-/

namespace ManuscriptAudit.NodalSwapCoverPatch

open NodalConductor NodalMilnorCoefficients NodalSwapCover Polynomial Matrix

noncomputable section

universe u

variable (K : Type u) [Field K]

local instance : Algebra (coordinates K) K := originAlgebra K

private def entries : Matrix (Fin 2) (Fin 2) (K × K) :=
  fun i j => if i = j then (1, 0) else (0, 1)

private theorem entries_square : entries K * entries K = 1 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Prod.ext <;>
    simp [entries, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

/-- The first branch sees the identity and the second branch sees the swap. -/
def transition : GL (Fin 2) (K × K) where
  val := entries K
  inv := entries K
  val_inv := entries_square K
  inv_val := entries_square K

abbrev SwapPatch :=
  MilnorCoordinatePatch.patch (branchMap K) (residueMap K) (transition K).val

private theorem transition_zero (c : Fin 2 → K) :
    ((transition K).val *ᵥ (residueMap K ∘ c)) 0 = (c 0, c 1) := by
  apply Prod.ext <;>
    simp [transition, entries, Matrix.mulVec, dotProduct, Fin.sum_univ_two, residueMap_apply]

private theorem transition_one (c : Fin 2 → K) :
    ((transition K).val *ᵥ (residueMap K ∘ c)) 1 = (c 1, c 0) := by
  apply Prod.ext <;>
    simp [transition, entries, Matrix.mulVec, dotProduct, Fin.sum_univ_two, residueMap_apply]

theorem patch_mem_iff (f : Fin 2 → K[X]) (c : Fin 2 → K) :
    (f, c) ∈ SwapPatch K ↔
      branchMap K (f 0) = (c 0, c 1) ∧ branchMap K (f 1) = (c 1, c 0) := by
  rw [MilnorCoordinatePatch.mem_patch_iff]
  constructor
  · intro h
    exact ⟨(congrFun h 0).trans (transition_zero K c),
      (congrFun h 1).trans (transition_one K c)⟩
  · rintro ⟨h₀, h₁⟩
    funext i
    fin_cases i
    · exact h₀.trans (transition_zero K c).symm
    · exact h₁.trans (transition_one K c).symm

/-- The two polynomial components of an element of the actual crossed algebra. -/
abbrev polynomialProjection : Cover K →ₐ[coordinates K] (K[X] × K[X]) :=
  (crossedPairs K).val

private def polynomials : Cover K →ₗ[coordinates K] (Fin 2 → K[X]) :=
  (LinearEquiv.finTwoArrow (coordinates K) K[X]).symm.toLinearMap.comp
    (polynomialProjection K).toLinearMap

private def evalAtOne : K[X] →ₐ[coordinates K] K where
  toRingHom := evalRingHom (1 : K)
  commutes' _ := rfl

private def scalars : Cover K →ₗ[coordinates K] (Fin 2 → K) :=
  ((evalAtOne K).toLinearMap.compLeft (Fin 2)).comp (polynomials K)

private def coverToPatch : Cover K →ₗ[coordinates K] SwapPatch K :=
  ((polynomials K).prod (scalars K)).codRestrict (SwapPatch K) fun z => by
    apply (patch_mem_iff K _ _).mpr
    refine ⟨Prod.ext rfl ?_, Prod.ext rfl ?_⟩
    · exact (condition K z).2
    · exact (condition K z).1.symm

private theorem coverToPatch_bijective : Function.Bijective (coverToPatch K) := by
  constructor
  · intro x y h
    have e := congrArg (fun z : SwapPatch K => z.val.1) h
    change (LinearEquiv.finTwoArrow (coordinates K) K[X]).symm x.val =
      (LinearEquiv.finTwoArrow (coordinates K) K[X]).symm y.val at e
    exact Subtype.ext ((LinearEquiv.finTwoArrow (coordinates K) K[X]).symm.injective e)
  · intro v
    have h := (patch_mem_iff K v.val.1 v.val.2).mp v.property
    have h₀₁ : (v.val.1 0).eval (-1) = v.val.2 1 := congrArg Prod.snd h.1
    have h₁₀ : (v.val.1 1).eval 1 = v.val.2 1 := congrArg Prod.fst h.2
    have h₀₀ : (v.val.1 0).eval 1 = v.val.2 0 := congrArg Prod.fst h.1
    have h₁₁ : (v.val.1 1).eval (-1) = v.val.2 0 := congrArg Prod.snd h.2
    let z : Cover K := ⟨(v.val.1 0, v.val.1 1), h₀₀.trans h₁₁.symm, h₀₁.trans h₁₀.symm⟩
    refine ⟨z, Subtype.ext (Prod.ext ?_ ?_)⟩
    · exact (LinearEquiv.finTwoArrow (coordinates K) K[X]).symm_apply_apply v.val.1
    · funext i
      fin_cases i
      · exact h₀₀
      · exact h₁₀

/-- The actual crossed algebra is exactly the Milnor patch as a module over the node. -/
def patchEquiv : Cover K ≃ₗ[coordinates K] SwapPatch K :=
  LinearEquiv.ofBijective (coverToPatch K) (coverToPatch_bijective K)

theorem patchEquiv_fst (z : Cover K) :
    (patchEquiv K z).val.1 =
      (LinearEquiv.finTwoArrow (coordinates K) K[X]).symm (polynomialProjection K z) :=
  rfl

theorem cover_finite_projective (h2 : (2 : K) ≠ 0) :
    Module.Finite (coordinates K) (Cover K) ∧ Module.Projective (coordinates K) (Cover K) := by
  obtain ⟨hFin, hProj⟩ := NodalMilnorCoefficients.finite_projective K (Fin 2) h2 (transition K)
  letI := hFin
  letI := hProj
  let e := (patchEquiv K).symm
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    Module.Projective.of_split e.symm.toLinearMap e.toLinearMap (by
      apply LinearMap.ext
      intro z
      exact e.apply_symm_apply z)⟩

end

end ManuscriptAudit.NodalSwapCoverPatch

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalSwapCoverPatch.patch_mem_iff,
        ``ManuscriptAudit.NodalSwapCoverPatch.patchEquiv,
        ``ManuscriptAudit.NodalSwapCoverPatch.patchEquiv_fst,
        ``ManuscriptAudit.NodalSwapCoverPatch.cover_finite_projective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
