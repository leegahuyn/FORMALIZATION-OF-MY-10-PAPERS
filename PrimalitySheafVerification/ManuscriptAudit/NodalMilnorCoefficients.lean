import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.MilnorIdentityRecovery
import PrimalitySheafVerification.ManuscriptAudit.NodalConductorSquare

/-!
# Milnor coefficients for the actual split node

The polynomial branch map records evaluation at 1 and -1. The residue
map repeats a scalar at the two branches. Their scalar pullback is the
actual nodal coordinate ring.
-/

namespace ManuscriptAudit.NodalMilnorCoefficients

open NodalConductor Polynomial Matrix

noncomputable section

universe u

variable (K : Type u) [Field K]

abbrev originAlgebra : Algebra (coordinates K) K :=
  (NodalConductorSquare.origin K).hom.toAlgebra

attribute [local instance] originAlgebra

def branchMap : K[X] →ₐ[coordinates K] (K × K) :=
  { (NodalConductorSquare.branches K).hom with
    commutes' := fun a => by
      change (a.val.eval 1, a.val.eval (-1)) = (a.val.eval 1, a.val.eval 1)
      exact Prod.ext rfl ((mem_equalBranchValues K a.val).mp
        (coordinates_le_equalBranchValues K a.property)).symm }

def residueMap : K →ₐ[coordinates K] (K × K) :=
  { (NodalConductorSquare.diagonal K).hom with
    commutes' := fun _ => rfl }

theorem branchMap_apply (f : K[X]) : branchMap K f = (f.eval 1, f.eval (-1)) :=
  rfl

theorem residueMap_apply (c : K) : residueMap K c = (c, c) :=
  rfl

theorem branchMap_surjective (h2 : (2 : K) ≠ 0) : Function.Surjective (branchMap K) :=
  NodalConductorSquare.branches_surjective K h2

theorem pairMap_bijective (h2 : (2 : K) ≠ 0) :
    Function.Bijective (MilnorIdentityGluing.pairMap (branchMap K) (residueMap K)) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : MilnorIdentityGluing.compatiblePair (branchMap K) (residueMap K) =>
      z.val.1) hab
  · rintro ⟨⟨f, c⟩, h⟩
    change (f.eval 1, f.eval (-1)) = (c, c) at h
    have h₁ : f.eval 1 = c := congrArg Prod.fst h
    have h₂ : f.eval (-1) = c := congrArg Prod.snd h
    have hf : f ∈ coordinates K := by
      rw [coordinates_eq_equalBranchValues K h2, mem_equalBranchValues]
      exact h₁.trans h₂.symm
    refine ⟨⟨f, hf⟩, Subtype.ext ?_⟩
    exact Prod.ext rfl h₁

variable (n : Type*) [Fintype n] [DecidableEq n]

private def identityPatchEquiv (h2 : (2 : K) ≠ 0) :
    MilnorCoordinatePatch.patch (branchMap K) (residueMap K) (1 : Matrix n n (K × K)) ≃ₗ[coordinates K]
      (n → coordinates K) := by
  have hPatch :
      MilnorCoordinatePatch.patch (branchMap K) (residueMap K) (1 : Matrix n n (K × K)) =
        MilnorIdentityGluing.identityPatch (branchMap K) (residueMap K) n := by
    apply Submodule.ext
    intro z
    rw [MilnorCoordinatePatch.mem_patch_one_iff]
    change (branchMap K ∘ z.1 = residueMap K ∘ z.2) ↔
      ∀ i, branchMap K (z.1 i) = residueMap K (z.2 i)
    exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  rw [hPatch]
  exact (MilnorIdentityGluing.identityPatchEquiv (branchMap K) (residueMap K) n
    (pairMap_bijective K h2)).symm

/-- Every invertible transition gives a finite projective patch over the actual split node. -/
theorem finite_projective (h2 : (2 : K) ≠ 0) (U : GL n (K × K)) :
    Module.Finite (coordinates K)
        (MilnorCoordinatePatch.patch (branchMap K) (residueMap K) U.val) ∧
      Module.Projective (coordinates K)
        (MilnorCoordinatePatch.patch (branchMap K) (residueMap K) U.val) :=
  MilnorProjectivePatch.finite_projective_of_identity (branchMap K) (residueMap K)
    (branchMap_surjective K h2) U (identityPatchEquiv K (n ⊕ n) h2)

/-- Base change of an invertible transition patch to K[t] recovers free coordinates. -/
theorem normalizationMap_bijective (h2 : (2 : K) ≠ 0) (U : GL n (K × K)) :
    Function.Bijective (MilnorNormalizationMap.normalizationMap (branchMap K) (residueMap K) U.val) :=
  MilnorIdentityRecovery.normalizationMap_bijective (branchMap K) (residueMap K)
    (branchMap_surjective K h2) (pairMap_bijective K h2) U

end

end ManuscriptAudit.NodalMilnorCoefficients

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
      [``ManuscriptAudit.NodalMilnorCoefficients.branchMap_surjective,
        ``ManuscriptAudit.NodalMilnorCoefficients.pairMap_bijective,
        ``ManuscriptAudit.NodalMilnorCoefficients.finite_projective,
        ``ManuscriptAudit.NodalMilnorCoefficients.normalizationMap_bijective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
