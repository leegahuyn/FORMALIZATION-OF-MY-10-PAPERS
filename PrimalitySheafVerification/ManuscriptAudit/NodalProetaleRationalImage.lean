import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothRationalBoundary
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveNormalization
import PrimalitySheafVerification.ManuscriptAudit.SplitClosedProetaleComplement

/-! The actual rational singular point has exact native pro-étale direct image. -/

namespace ManuscriptAudit.NodalProetaleRationalImage

open AlgebraicGeometry CategoryTheory
open NodalProjectiveClosure (projectiveNodeToBase)
open NodalProjectiveNormalization (smoothInclusion smoothInclusion_quasiCompact)
open NodalSmoothLocusOverlap (smoothOpen)
open NodalSmoothRationalBoundary
open SplitClosedProetaleComplement (baseComplement chart_quasiCompact)
open ProetaleBaseChange (directImage)

noncomputable section
universe v

variable (K : Type) [Field K]

theorem map_epi
    {F G : Sheaf (Scheme.ProEt.topology (Spec (CommRingCat.of K))) AddCommGrpCat.{v}}
    (a : F ⟶ G) [Epi a] :
    Epi ((directImage (projectiveOrigin K) AddCommGrpCat.{v}).map a) := by
  letI := projectiveOrigin_closed K
  have hOpen : baseComplement (projectiveOrigin K) = smoothOpen K := by
    apply SetLike.coe_injective
    change (Set.range (projectiveOrigin K))ᶜ = ↑(smoothOpen K)
    rw [← smooth_range K, Scheme.Opens.range_ι]
  have hQC : QuasiCompact (baseComplement (projectiveOrigin K)).ι := by
    rw [hOpen]
    exact smoothInclusion_quasiCompact K
  exact SplitClosedProetaleDirectImage.map_epi (projectiveOrigin K) (projectiveNodeToBase K)
    (projectiveOrigin_overBase K) (fun U _ ↦ chart_quasiCompact (projectiveOrigin K) hQC U) a

end
end ManuscriptAudit.NodalProetaleRationalImage

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalProetaleRationalImage.map_epi
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{name} depends on unexpected axioms {ax}"
  logInfo m!"{name} uses {ax}"
