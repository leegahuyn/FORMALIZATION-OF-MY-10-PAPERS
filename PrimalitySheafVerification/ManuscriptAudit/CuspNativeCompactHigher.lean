import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProperHigher
import PrimalitySheafVerification.ManuscriptAudit.CuspProperTwoBoundaryPoints
import PrimalitySheafVerification.ManuscriptAudit.ProetaleHigherShortExactEquiv
import PrimalitySheafVerification.ManuscriptAudit.ProetaleExactDirectImageCohomology
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleComplement

/-! The actual rational boundary contributes no positive native
cohomology, so the two compact support groups agree with the proper
cusp in every degree at least two. -/

namespace ManuscriptAudit.CuspNativeCompactHigher

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp projectiveCuspToBase projectiveCusp_isProper affineOpen)
open CuspNativeCompactSmoothHOne (smoothOpen properOrigin_closed)
open CuspProperTwoBoundaryPoints (origin boundary_disjoint smoothOpen_range smoothOpen_quasiCompact)
open CuspRationalInfinity (infinityPoint infinityPoint_isClosedImmersion infinityPoint_overBase)
open SmallEtaleGeometricBaseChange (cuspOrigin)
open ProetaleContinuousDirectImageMaps (functions functionsOver)
open OpenProetaleExtension (extensionByZero)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleBaseChange (directImage)
open ProetaleAdicClosedPairSupport (boundary)
open SplitClosedProetaleComplement (baseComplement chart_quasiCompact)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (l : ℕ) [Fact l.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev X := projectiveCusp K
private abbrev s := projectiveCuspToBase K

private instance cusp_locallyNoetherian : IsLocallyNoetherian (X K) := by
  letI := projectiveCusp_isProper K
  exact LocallyOfFiniteType.isLocallyNoetherian (s K)

private theorem origin_overBase : origin K ≫ s K = 𝟙 (Spec (CommRingCat.of K)) := by
  have h : CommRingCat.ofHom (algebraMap K (CuspPunctured.CuspSubalgebra K)) ≫
      CuspConductorSquare.origin K = 𝟙 (CommRingCat.of K) := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    change (Polynomial.constantCoeff : Polynomial K →+* K) (Polynomial.C a) = a
    simp
  rw [origin, Category.assoc, CuspProperCompactification.affineOpen_toBase, cuspOrigin,
    ← Spec.map_comp, h, Spec.map_id]

private theorem closed_H_succ (i : Spec (CommRingCat.of K) ⟶ X K) [IsClosedImmersion i]
    (hi : i ≫ s K = 𝟙 _) (n : ℕ) :
    Subsingleton (Sheaf.H (functionsOver ℤ_[l] i) (n + 1)) := by
  letI : (directImage i A).PreservesEpimorphisms :=
    { preserves f := SplitClosedProetaleDirectImage.map_epi i (s K) hi
        (fun U _ ↦ chart_quasiCompact i inferInstance U) f }
  letI := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K
    (functions ℤ_[l] (Spec (CommRingCat.of K))) n
  exact (ProetaleExactDirectImageCohomology.continuousEquiv i ℤ_[l] (n + 1)).injective.subsingleton

private theorem boundary_H_succ (n : ℕ) :
    Subsingleton (Sheaf.H (boundary (origin K) (infinityPoint K) l) (n + 1)) := by
  let i := origin K
  let j := infinityPoint K
  letI : IsClosedImmersion i := properOrigin_closed K
  letI : IsClosedImmersion j := infinityPoint_isClosedImmersion K
  let F := functionsOver ℤ_[l] i
  let G := functionsOver ℤ_[l] j
  let e := cohomologyIso (X := X K) (biprod.isoProd F G).symm (n + 1)
  let p : Sheaf.H (F ⊞ G) (n + 1) ≃+ Sheaf.H F (n + 1) × Sheaf.H G (n + 1) :=
    Ext.addEquivBiprod
  have hF := closed_H_succ K l i (origin_overBase K) n
  have hG := closed_H_succ K l j (infinityPoint_overBase K) n
  exact ⟨fun x y ↦ (e.trans p).injective (Prod.ext (hF.elim _ _) (hG.elim _ _))⟩

set_option maxHeartbeats 5300000 in
/-- Actual affine cusp compact support and its proper ambient group agree from degree two. -/
def affineEquiv (n : ℕ) :
    Sheaf.H ((extensionByZero (affineOpen K) A).obj (functions ℤ_[l] _)) (n + 2) ≃+
      (X K).EllAdicCohomology l (n + 2) := by
  let i := infinityPoint K
  letI : IsClosedImmersion i := infinityPoint_isClosedImmersion K
  let S := ProetaleAdicClosedRestrictionEpi.sequence i l
  let hS := ProetaleAdicClosedRestrictionEpi.sequence_shortExact i l
  let e := ProetaleAdicClosedSupportKernel.extensionKernelIso i (affineOpen K) l
    (by rw [← CuspInfinitySupport.affine_complement_eq_infinity K, compl_compl])
  exact (cohomologyIso e (n + 2)).trans
    (ProetaleHigherShortExactEquiv.equivalence S hS (n + 1)
      (closed_H_succ K l i (infinityPoint_overBase K) n)
      (closed_H_succ K l i (infinityPoint_overBase K) (n + 1)))

set_option maxHeartbeats 5300000 in
/-- The actual smooth affine cusp compact group also agrees with the ambient from degree two. -/
def smoothEquiv (n : ℕ) :
    Sheaf.H ((extensionByZero (smoothOpen K) A).obj (functions ℤ_[l] _)) (n + 2) ≃+
      (X K).EllAdicCohomology l (n + 2) := by
  let i := origin K
  let j := infinityPoint K
  letI : IsClosedImmersion i := properOrigin_closed K
  letI : IsClosedImmersion j := infinityPoint_isClosedImmersion K
  letI : QuasiCompact (smoothOpen K) := smoothOpen_quasiCompact K
  let S := ProetaleAdicClosedPairEpi.sequence i j l
  let hS := ProetaleAdicClosedPairEpi.sequence_shortExact i j l (boundary_disjoint K)
  let e := ProetaleAdicClosedPairSupport.extensionKernelIso i j l (smoothOpen K) (smoothOpen_range K)
  exact (cohomologyIso e (n + 2)).trans
    (ProetaleHigherShortExactEquiv.equivalence S hS (n + 1)
      (boundary_H_succ K l n) (boundary_H_succ K l (n + 1)))

variable (p : ℕ) [hp : Fact p.Prime] [hK : CharP K p] [hl : NeZero (l : K)]

include p hp hK hl in
/-- Actual affine compact cusp cohomology vanishes in positive characteristic from degree three. -/
theorem affine_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H ((extensionByZero (affineOpen K) A).obj (functions ℤ_[l] _)) (n + 3)) := by
  let e := affineEquiv K l (n + 1)
  have h := CuspNativeProperHigher.adic_add_three_subsingleton K p l n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

include p hp hK hl in
/-- The actual compact cohomology of the punctured cusp also vanishes from degree three. -/
theorem smooth_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H ((extensionByZero (smoothOpen K) A).obj (functions ℤ_[l] _)) (n + 3)) := by
  let e := smoothEquiv K l (n + 1)
  have h := CuspNativeProperHigher.adic_add_three_subsingleton K p l n
  exact ⟨fun a b ↦ e.injective (h.elim (e a) (e b))⟩

end
end ManuscriptAudit.CuspNativeCompactHigher

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeCompactHigher.affineEquiv,
      ``ManuscriptAudit.CuspNativeCompactHigher.smoothEquiv,
      ``ManuscriptAudit.CuspNativeCompactHigher.affine_subsingleton,
      ``ManuscriptAudit.CuspNativeCompactHigher.smooth_subsingleton] do
    let ax ← collectAxioms name
    unless ax.all (fun a ↦ allowed.contains a) do
      throwError m!"{name} depends on unexpected axioms {ax}"
    logInfo m!"{name} uses {ax}"
