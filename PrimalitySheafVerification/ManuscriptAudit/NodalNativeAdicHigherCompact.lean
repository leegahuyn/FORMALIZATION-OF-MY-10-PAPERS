import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleHigherShortExactEquiv
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeHigherNormalization
import PrimalitySheafVerification.ManuscriptAudit.NativeCurveCompactAdicHTwo

/-! Removing the two literal rational boundary points of the affine smooth node
preserves actual integral adic cohomology in every degree at least two. -/

namespace ManuscriptAudit.NodalNativeAdicHigherCompact

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase projectiveNode_isProper affineOpen)
open NodalProjectiveNormalization (normalizedNode)
open NodalRationalInfinity (infinityPoint infinityPoint_overBase infinityPoint_isClosedImmersion
  affine_complement_eq_infinity)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalAffineSmoothCompactOpen (compactOpen compactOpen_range compactOpen_quasiCompact boundary_disjoint)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open ProetaleAdicClosedPairSupport (boundary extensionKernelIso)
open OpenProetaleExtension (extensionByZero)
open SplitClosedProetaleComplement (baseComplement chart_quasiCompact)
open ProetaleBaseChange (directImage)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (l : ℕ) [Fact l.Prime]

private abbrev A := AddCommGrpCat.{1}

private theorem infinityImage_preserves :
    (directImage (infinityPoint K) A).PreservesEpimorphisms where
  preserves a := by
    letI := infinityPoint_isClosedImmersion K
    letI := projectiveNode_isProper K
    letI : QuasiSeparatedSpace (projectiveNode K) :=
      quasiSeparatedSpace_of_quasiSeparated (projectiveNodeToBase K)
    have hRange : (↑(baseComplement (infinityPoint K)) : Set (projectiveNode K)) =
        Set.range (affineOpen K) := by
      change (Set.range (infinityPoint K))ᶜ = _
      rw [← affine_complement_eq_infinity K, compl_compl]
    letI : CompactSpace (baseComplement (infinityPoint K)) :=
      isCompact_iff_compactSpace.mp (hRange.symm ▸ isCompact_range (affineOpen K).continuous)
    let hQC := quasiCompact_of_compactSpace (baseComplement (infinityPoint K)).ι
    exact SplitClosedProetaleDirectImage.map_epi (infinityPoint K) (projectiveNodeToBase K)
      (infinityPoint_overBase K) (fun U _ ↦ chart_quasiCompact (infinityPoint K) hQC U) a

private theorem infinity_H_succ (n : ℕ) :
    Subsingleton (Sheaf.H (functionsOver ℤ_[l] (infinityPoint K)) (n + 1)) := by
  letI := infinityImage_preserves K
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K
    (functions ℤ_[l] (Spec (CommRingCat.of K))) n
  exact (ProetaleExactDirectImageCohomology.continuousEquiv
    (infinityPoint K) ℤ_[l] (n + 1)).injective.subsingleton

private theorem boundary_H_succ (n : ℕ) :
    Subsingleton (Sheaf.H (boundary (projectiveOrigin K) (infinityPoint K) l) (n + 1)) := by
  let F := functionsOver ℤ_[l] (projectiveOrigin K)
  let G := functionsOver ℤ_[l] (infinityPoint K)
  let e := ProetaleCohomologyIso.cohomologyIso (X := projectiveNode K)
    (biprod.isoProd F G).symm (n + 1)
  let p : Sheaf.H (F ⊞ G) (n + 1) ≃+ Sheaf.H F (n + 1) × Sheaf.H G (n + 1) :=
    Ext.addEquivBiprod
  let hF := NodalNativeHigherNormalization.rationalImage_H_succ K ℤ_[l] n
  let hG := infinity_H_succ K l n
  exact ⟨fun x y ↦ (e.trans p).injective (Prod.ext (hF.elim _ _) (hG.elim _ _))⟩

/-- Compactly supported cohomology of the actual smooth affine node compares with
ordinary cohomology of its proper closure. -/
def properEquiv (n : ℕ) :
    Sheaf.H ((extensionByZero (compactOpen K) A).obj (functions ℤ_[l] _)) (n + 2) ≃+
      (projectiveNode K).EllAdicCohomology l (n + 2) := by
  letI := projectiveOrigin_closed K
  letI := infinityPoint_isClosedImmersion K
  letI := compactOpen_quasiCompact K
  let i := projectiveOrigin K
  let j := infinityPoint K
  let S := ProetaleAdicClosedPairEpi.sequence i j l
  let hS := ProetaleAdicClosedPairEpi.sequence_shortExact i j l (boundary_disjoint K)
  let e := extensionKernelIso i j l (compactOpen K) (compactOpen_range K)
  exact (ProetaleCohomologyIso.cohomologyIso (X := projectiveNode K) e (n + 2)).trans
    (ProetaleHigherShortExactEquiv.equivalence S hS (n + 1)
      (boundary_H_succ K l n) (boundary_H_succ K l (n + 1)))

/-- The same compact groups compare with ordinary cohomology on the actual normalization. -/
def normalizationEquiv (h2 : (2 : K) ≠ 0) (n : ℕ) :
    Sheaf.H ((extensionByZero (compactOpen K) A).obj (functions ℤ_[l] _)) (n + 2) ≃+
      (normalizedNode K).EllAdicCohomology l (n + 2) :=
  (properEquiv K l n).trans (NodalNativeHigherNormalization.adicEquiv K l h2 n)

end
end ManuscriptAudit.NodalNativeAdicHigherCompact

open Lean Elab Command in
run_cmd do
  for name in [``ManuscriptAudit.NodalNativeAdicHigherCompact.properEquiv,
      ``ManuscriptAudit.NodalNativeAdicHigherCompact.normalizationEquiv] do
    let ax ← collectAxioms name
    let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
