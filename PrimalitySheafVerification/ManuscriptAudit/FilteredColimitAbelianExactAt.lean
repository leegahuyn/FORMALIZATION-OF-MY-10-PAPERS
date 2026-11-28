import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! Exactness of a diagram of actual abelian groups survives its
filtered colimits. The element argument retains an actual stage
for both the cocycle and its primitive. -/

namespace ManuscriptAudit.FilteredColimitAbelianExactAt

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe v u w

variable {I : Type u} [Category.{v} I] [IsFiltered I]
  [PreservesFilteredColimitsOfSize.{v,u} (CategoryTheory.forget AddCommGrpCat.{w})]
  {F G H : I ⥤ AddCommGrpCat.{w}} (a : F ⟶ G) (b : G ⟶ H)
  {cF : Cocone F} {cG : Cocone G} {cH : Cocone H}
  (f : cF.pt ⟶ cG.pt) (g : cG.pt ⟶ cH.pt)

set_option maxHeartbeats 3500000 in
/-- Build exactness on the actual colimit groups from exactness on
each stage and compatibility of the two actual colimit maps. -/
theorem exact_of_diagram (hG : IsColimit cG) (hH : IsColimit cH)
    (hf : ∀ i, cF.ι.app i ≫ f = a.app i ≫ cG.ι.app i)
    (hg : ∀ i, cG.ι.app i ≫ g = b.app i ≫ cH.ι.app i)
    (h : f ≫ g = 0) (hStage : ∀ i (x : G.obj i), b.app i x = 0 → ∃ y, a.app i y = x) :
    (ShortComplex.mk f g h).Exact := by
  rw [(ShortComplex.mk f g h).ab_exact_iff]
  intro x hx
  change g x = 0 at hx
  let K := CategoryTheory.forget AddCommGrpCat.{w}
  let tG := isColimitOfPreserves K hG
  let tH := isColimitOfPreserves K hH
  obtain ⟨i, y, hy⟩ := Types.jointly_surjective_of_isColimit tG x
  have h₁ : (cH.ι.app i) (b.app i y) = (cH.ι.app i) 0 := by
    have he := congrArg (fun r : G.obj i ⟶ cH.pt ↦ r y) (hg i)
    change g (cG.ι.app i y) = cH.ι.app i (b.app i y) at he
    change cG.ι.app i y = x at hy
    rw [hy, hx] at he
    rw [← he, map_zero]
  obtain ⟨j, ij, h₂⟩ := (Types.FilteredColimit.isColimit_eq_iff' tH (b.app i y) 0).mp h₁
  change H.map ij (b.app i y) = H.map ij 0 at h₂
  have h₃ : b.app j (G.map ij y) = 0 := by
    have he := congrArg (fun r : G.obj i ⟶ H.obj j ↦ r y) (b.naturality ij)
    change b.app j (G.map ij y) = H.map ij (b.app i y) at he
    exact he.trans (h₂.trans (map_zero _))
  obtain ⟨z, hz⟩ := hStage j (G.map ij y) h₃
  refine ⟨cF.ι.app j z, ?_⟩
  have hF := congrArg (fun r : F.obj j ⟶ cG.pt ↦ r z) (hf j)
  change f (cF.ι.app j z) = cG.ι.app j (a.app j z) at hF
  have hNat := congrArg (fun r : G.obj i ⟶ cG.pt ↦ r y) (cG.w ij)
  change cG.ι.app j (G.map ij y) = cG.ι.app i y at hNat
  exact hF.trans ((congrArg (cG.ι.app j) hz).trans (hNat.trans hy))

end
end ManuscriptAudit.FilteredColimitAbelianExactAt

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.FilteredColimitAbelianExactAt.exact_of_diagram
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
