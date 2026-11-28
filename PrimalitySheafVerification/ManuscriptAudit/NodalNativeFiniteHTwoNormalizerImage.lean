import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalNativeConductorHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFiniteClosedImageHTwo

/-! The genuine conductor sequence identifies the actual finite-coefficient degree-two
cohomology of the node with that of the normalization coefficient's direct image. -/

namespace ManuscriptAudit.NodalNativeFiniteHTwoNormalizerImage

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open NodalProjectiveClosure (projectiveNode)
open NodalSmoothRationalBoundary (projectiveOrigin projectiveOrigin_closed)
open NodalProjectiveNormalization (normalizationMap normalizedNode)
open NodalProetaleConductorSequence (sequence sequence_shortExact)
open ProetaleContinuousDirectImageMaps (functions functionsOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [IsTopologicalAddGroup M] [Finite M]

private abbrev integers :=
  (constantSheaf (Scheme.ProEt.topology (projectiveNode K)) AddCommGrpCat.{1}).obj
    (AddCommGrpCat.of (ULift.{1} ℤ))

/-- Positive cohomology of the rational conductor support does not contribute
to the degree-two comparison with the actual normalization coefficient image. -/
def normalizationImageEquiv (h2 : (2 : K) ≠ 0) :
    Sheaf.H (functions M (projectiveNode K)) 2 ≃+
      Sheaf.H (functionsOver M (normalizationMap K)) 2 := by
  letI := projectiveOrigin_closed K
  let S := sequence K h2 M
  let hS := sequence_shortExact K h2 M
  let F := functions M (Spec (CommRingCat.of K))
  letI : Subsingleton (Sheaf.H F 1) := ProetaleAlgebraicallyClosedCohomology.H_succ_subsingleton K F 0
  have hOne : Subsingleton (Sheaf.H S.X₃ 1) :=
    ProetaleDirectImageHOne.directImage_HOne_subsingleton (projectiveOrigin K) F
  have hTwo : Subsingleton (Sheaf.H S.X₃ 2) :=
    ProetaleFiniteClosedImageHTwo.HTwo_subsingleton (projectiveOrigin K) M
  refine AddEquiv.ofBijective (Sheaf.H.map S.f 2) ⟨?_, ?_⟩
  · intro x y hxy
    apply sub_eq_zero.mp
    have h0 : Sheaf.H.map S.f 2 (x-y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (X := integers K) hS (x-y) h0
      (show 1+1=2 by rfl)
    have hz₀ : z = 0 := hOne.elim _ _
    rw [hz₀, Ext.zero_comp] at hz
    exact hz.symm
  · intro x
    have hx : Sheaf.H.map S.g 2 x = 0 := hTwo.elim _ _
    exact Ext.covariant_sequence_exact₂ (integers K) hS x hx

end
end ManuscriptAudit.NodalNativeFiniteHTwoNormalizerImage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalNativeFiniteHTwoNormalizerImage.normalizationImageEquiv
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
