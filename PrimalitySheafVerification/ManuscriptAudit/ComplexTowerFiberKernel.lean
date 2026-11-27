import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ComplexTowerDifference

/-! The native mapping fiber has the expected homology kernel when the preceding difference is epic. -/

namespace ManuscriptAudit.ComplexTowerFiberKernel

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open ComplexTowerDifference (difference mappingFiber toProduct triangle triangle_distinguished homology_exact)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

private abbrev A := AddCommGrpCat.{0}
private abbrev Ch := CochainComplex A ℤ

variable [HasDerivedCategory A]
variable (K : ℕ → Ch) (transition : ∀ r, K (r + 1) ⟶ K r)

/-- If the preceding difference is epic on homology, then projection of the
mapping fiber is monic on homology in the current degree. -/
theorem homology_projection_mono (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    [Epi (homologyMap (difference K transition) n₀)] :
    Mono (homologyMap (toProduct K transition) n₁) := by
  let T := triangle K transition
  let hT := triangle_distinguished K transition
  let δ := CochainComplex.homologyδOfTriangle T n₀ n₁ hn
  have hd : δ = 0 :=
    (cancel_epi (homologyMap (difference K transition) n₀)).mp
      ((CochainComplex.homologyMap_homologyδOfTriangle T hT n₀ n₁ hn).trans
        (comp_zero _).symm)
  let S := ShortComplex.mk δ (homologyMap (toProduct K transition) n₁)
    (CochainComplex.homologyδOfTriangle_homologyMap T hT n₀ n₁ hn)
  have hS : S.Exact := CochainComplex.homologyMap_exact₁_of_distTriang T hT n₀ n₁ hn
  exact (S.exact_iff_mono hd).mp hS

/-- The homology of the actual mapping fiber is the kernel of the actual product
difference on homology, when the preceding product difference is epic. -/
def homologyKernelIso (n₀ n₁ : ℤ) (hn : n₀ + 1 = n₁)
    [Epi (homologyMap (difference K transition) n₀)] :
    (mappingFiber K transition).homology n₁ ≅ kernel (homologyMap (difference K transition) n₁) := by
  let f := homologyMap (toProduct K transition) n₁
  let g := homologyMap (difference K transition) n₁
  let S := ShortComplex.mk f g
    (CochainComplex.homologyMap_comp_eq_zero_of_distTriang (triangle K transition)
      (triangle_distinguished K transition) n₁)
  letI : Mono S.f := homology_projection_mono K transition n₀ n₁ hn
  have hS : S.Exact := homology_exact K transition n₁
  exact hS.fIsKernel.conePointUniqueUpToIso (kernelIsKernel g)

end
end ManuscriptAudit.ComplexTowerFiberKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ComplexTowerFiberKernel.homology_projection_mono,
      ``ManuscriptAudit.ComplexTowerFiberKernel.homologyKernelIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
