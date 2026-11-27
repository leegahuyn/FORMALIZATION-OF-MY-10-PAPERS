import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeAdicHTwoLower

/-! The image of the actual integral Laurent class is the kernel of the two-chart obstruction. -/

namespace ManuscriptAudit.CuspNativeAdicHTwoObstruction

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineOpen)
open CuspProperYChart (lineOpen)
open CuspNativeProetaleHTwoLower (overlapOpen fstLeg sndLeg overlap cover)
open CuspNativeAdicHTwoLower (overlapEquiv adicInclusion)
open ProetaleContinuousDirectImageMaps (functions)
open ProetaleMayerVietorisSite (coverComplex coverComplex_shortExact)
open ProetaleMayerVietorisConnecting (firstEquiv lastEquiv connecting extBoundary)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev l := overlapOpen K
private abbrev F := functions ℤ_[ℓ] (X K)
private abbrev S := coverComplex (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K)

private abbrev e₁ :=
  firstEquiv (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1

private abbrev e₂ :=
  lastEquiv (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 2

private abbrev boundary :=
  extBoundary (j K) (k K) (l K) (fstLeg K) (sndLeg K) (overlap K) (cover K) (F K ℓ) 1

/-- The actual map to cohomology of the two-chart free term in Mayer–Vietoris. -/
def obstruction : (X K).EllAdicCohomology ℓ 2 →+ Ext (S K).X₂ (F K ℓ) 2 :=
  ((Ext.mk₀ (S K).g).precomp (F K ℓ) (zero_add 2)).comp (e₂ K ℓ).symm.toAddMonoidHom

theorem range_eq_ker : (adicInclusion K ℓ).range = (obstruction K ℓ).ker := by
  let hS := coverComplex_shortExact (j K) (k K) (l K) (fstLeg K) (sndLeg K)
    (overlap K) (cover K)
  have h := Ext.contravariant_sequence_exact₃' hS (F K ℓ) 1 2 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  ext x
  constructor
  · rintro ⟨a, rfl⟩
    let v := (e₁ K ℓ).symm ((overlapEquiv K ℓ).symm a)
    have hv : (e₂ K ℓ).symm (adicInclusion K ℓ a) = boundary K ℓ v := by
      change (e₂ K ℓ).symm ((e₂ K ℓ) (boundary K ℓ v)) = _
      exact (e₂ K ℓ).symm_apply_apply _
    change (Ext.mk₀ (S K).g).comp ((e₂ K ℓ).symm (adicInclusion K ℓ a)) (zero_add 2) = 0
    exact (h _).2 ⟨v, hv.symm⟩
  · intro hx
    change (Ext.mk₀ (S K).g).comp ((e₂ K ℓ).symm x) (zero_add 2) = 0 at hx
    obtain ⟨v, hv⟩ := (h _).1 hx
    refine ⟨overlapEquiv K ℓ (e₁ K ℓ v), ?_⟩
    change boundary K ℓ v = (e₂ K ℓ).symm x at hv
    change (e₂ K ℓ) (boundary K ℓ
      ((e₁ K ℓ).symm ((overlapEquiv K ℓ).symm (overlapEquiv K ℓ (e₁ K ℓ v))))) = x
    rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply, hv,
      AddEquiv.apply_symm_apply]

end
end ManuscriptAudit.CuspNativeAdicHTwoObstruction

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspNativeAdicHTwoObstruction.range_eq_ker
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
