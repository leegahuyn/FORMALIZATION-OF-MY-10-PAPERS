import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSwapCoverLocalTrace
import PrimalitySheafVerification.ManuscriptAudit.SheafHOneGlobalBoundary
import PrimalitySheafVerification.ManuscriptAudit.SheafObjectwiseKernel
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# An actual ordinary étale H¹ class of the split affine node

The diagonal and trace form a short exact sequence. Its constant
section 1 does not lift globally because the crossed cover is
connected, although it lifts étale locally.
-/

namespace ManuscriptAudit.NodalSwapCoverHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalConductor NodalSwapCover NodalSwapCoverSheafTrace
open AffineEtaleTensorPresentation

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev A : Type := ↥(coordinates K)
private abbrev E : Type := Cover K
private abbrev R := CommRingCat.of (A K)
private abbrev X := Spec (R K)
private abbrev J := Scheme.AffineEtale.topology (X K)
private abbrev term := KummerAffineCohomology.affineTerminal (R K)
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
attribute [local instance] KummerCohomologySequence.affineSiteHasExt
  SmallEtaleCohomologyComparison.fullSiteHasExt

private theorem twoTorsion (m : cyclic) : m + m = 0 := by
  change (m : ZMod 2) + m = 0
  rw [← two_mul, show (2 : ZMod 2) = 0 by decide, zero_mul]

variable (h2 : (2 : K) ≠ 0)

private theorem zero_condition : diagonal K cyclic ≫ trace K cyclic h2 = 0 :=
  SheafObjectwiseKernel.zero_of_value_kernel (diagonal K cyclic) (trace K cyclic h2)
    (fun U s => trace_app_kernel K cyclic h2 twoTorsion U.unop s)

def shortComplex : ShortComplex (Sheaf (J K) AddCommGrpCat.{0}) :=
  ShortComplex.mk (diagonal K cyclic) (trace K cyclic h2) (zero_condition K h2)

theorem shortComplex_shortExact : (shortComplex K h2).ShortExact := by
  have hinj (U : (X K).AffineEtaleᵒᵖ) :=
    diagonal_app_injective K cyclic h2 U.unop
  have hker (U : (X K).AffineEtaleᵒᵖ) (s : (coverFunctions K cyclic).obj.obj U) :=
    trace_app_kernel K cyclic h2 twoTorsion U.unop s
  apply ShortComplex.ShortExact.mk'
  · exact (shortComplex K h2).exact_of_f_is_kernel
      (SheafObjectwiseKernel.isLimit_of_value_kernel (diagonal K cyclic) (trace K cyclic h2)
        hinj hker (zero_condition K h2))
  · exact SheafObjectwiseKernel.mono_of_value_injective (diagonal K cyclic) hinj
  · exact NodalSwapCoverLocalTrace.trace_epi K cyclic h2

attribute [local instance] objectAlgebra

private def terminalTensorIso :
    Spec (CommRingCat.of (E K)) ≅ tensorScheme (A K) (E K) (term K) :=
  (IsPullback.id_vert (affineMap (A K) (E K))).isoPullback ≪≫
    (tensorIsoPullback (A K) (E K) (term K)).symm

include h2 in
private theorem terminal_tensor_connected :
    ConnectedSpace (tensorScheme (A K) (E K) (term K)) := by
  letI : ConnectedSpace (Spec (CommRingCat.of (E K))) :=
    NodalSwapCoverConnected.connected_spectrum K h2
  let e := terminalTensorIso K
  have hs : Function.Surjective e.hom := by
    intro p
    refine ⟨e.inv p, ?_⟩
    exact congrArg (fun f : tensorScheme (A K) (E K) (term K) ⟶
      tensorScheme (A K) (E K) (term K) => f p) e.inv_hom_id
  exact hs.connectedSpace e.hom.continuous

def terminalOne : (baseFunctions K cyclic).obj.obj (op (term K)) :=
  ContinuousMap.const (PrimeSpectrum (A K)) (1 : ZMod 2)

theorem terminal_one_unlifted :
    ¬ ∃ s : (coverFunctions K cyclic).obj.obj (op (term K)),
      (trace K cyclic h2).hom.app (op (term K)) s = terminalOne K := by
  rintro ⟨s, hs⟩
  letI : ConnectedSpace (tensorScheme (A K) (E K) (term K)) := terminal_tensor_connected K h2
  rw [trace_app_eq_zero_of_connected_tensor K cyclic h2 twoTorsion (term K) s] at hs
  change (0 : C(PrimeSpectrum (A K), ZMod 2)) = ContinuousMap.const _ 1 at hs
  exact zero_ne_one (congrArg (fun z : C(PrimeSpectrum (A K), ZMod 2) =>
    z (⊥ : PrimeSpectrum (A K))) hs)

/-- The actual connecting class of the constant trace section 1. -/
def affineFunctionHOneClass : Sheaf.H (baseFunctions K cyclic) 1 :=
  SheafHOneGlobalBoundary.boundaryAtTerminal (shortComplex K h2) (shortComplex_shortExact K h2)
    (KummerAffineCohomology.affineTerminal_isTerminal (R K)) (terminalOne K)

theorem affineFunctionHOneClass_ne_zero : affineFunctionHOneClass K h2 ≠ 0 := by
  intro h
  exact (terminal_one_unlifted K h2)
    ((SheafHOneGlobalBoundary.boundaryAtTerminal_eq_zero_iff
      (shortComplex K h2) (shortComplex_shortExact K h2)
      (KummerAffineCohomology.affineTerminal_isTerminal (R K)) (terminalOne K)).mp h)

include h2 in
theorem affine_function_HOne_nontrivial : Nontrivial (Sheaf.H (baseFunctions K cyclic) 1) :=
  SheafHOneGlobalBoundary.hOne_nontrivial_of_unlifted_global_section
    (shortComplex K h2) (shortComplex_shortExact K h2)
    (KummerAffineCohomology.affineTerminal_isTerminal (R K)) (terminalOne K)
    (terminal_one_unlifted K h2)

private def constantIso :
    (constantSheaf (J K) AddCommGrpCat.{0}).obj cyclic ≅ baseFunctions K cyclic :=
  let e := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
  e.unitIso.app _ ≪≫ e.inverse.mapIso
    ((SmallEtaleCohomologyComparison.constantComparison (R K)).app cyclic ≪≫
      EtaleContinuousMapSheaf.constantSheafContinuousMapIso (X K) cyclic)

private def classTransport :
    Sheaf.H (baseFunctions K cyclic) 1 ≃+
      Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 :=
  (((Sheaf.functorH (J K) 1).mapIso (constantIso K)).addCommGroupIsoToAddEquiv).symm.trans
    (SmallEtaleCohomologyComparison.cohomologyEquiv (R K) cyclic 1)

/-- The same class on the full small étale site with constant Z/2. -/
def fullConstantHOneClass :
    Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 :=
  classTransport K (affineFunctionHOneClass K h2)

theorem fullConstantHOneClass_ne_zero : fullConstantHOneClass K h2 ≠ 0 := by
  intro h
  apply affineFunctionHOneClass_ne_zero K h2
  apply (classTransport K).injective
  change classTransport K (affineFunctionHOneClass K h2) = 0 at h
  simpa only [map_zero] using h

include h2 in
/-- Ordinary native small étale H¹ of the split affine node with constant Z/2 is nonzero. -/
theorem full_constant_HOne_nontrivial :
    Nontrivial (Sheaf.H ((constantSheaf (X K).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1) :=
  ⟨⟨fullConstantHOneClass K h2, 0, fullConstantHOneClass_ne_zero K h2⟩⟩

end

end ManuscriptAudit.NodalSwapCoverHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in
    [``ManuscriptAudit.NodalSwapCoverHOne.shortComplex_shortExact,
      ``ManuscriptAudit.NodalSwapCoverHOne.affine_function_HOne_nontrivial,
      ``ManuscriptAudit.NodalSwapCoverHOne.affineFunctionHOneClass_ne_zero,
      ``ManuscriptAudit.NodalSwapCoverHOne.fullConstantHOneClass_ne_zero,
      ``ManuscriptAudit.NodalSwapCoverHOne.full_constant_HOne_nontrivial] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter (fun axiomName => !allowed.contains axiomName)
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
