import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! Compatibility of the canonical cokernel comparisons under composition
of exact restriction functors. -/

namespace ManuscriptAudit.PreservedCokernelComposition

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
variable [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
variable [HasCokernels C] [HasCokernels D] [HasCokernels E]
variable (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
variable [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms] [H.PreservesZeroMorphisms]
variable [PreservesFiniteColimits F] [PreservesFiniteColimits G] [PreservesFiniteColimits H]
variable (e : F ⋙ G ≅ H) {A B : C} (f : A ⟶ B)

/-- The cokernel isomorphism induced by the actual functor comparison. -/
def inducedCokernelIso : cokernel (G.map (F.map f)) ≅ cokernel (H.map f) :=
  cokernel.mapIso _ _ (e.app A) (e.app B) (e.hom.naturality f)

private theorem induced_π :
    cokernel.π (G.map (F.map f)) ≫ (inducedCokernelIso F G H e f).hom =
      (e.app B).hom ≫ cokernel.π (H.map f) := by
  unfold inducedCokernelIso
  simp [cokernel.mapIso]

/-- The cokernel comparison for two successive restrictions is the
canonical comparison for their composite. -/
theorem cokernelComparisons_compose :
    G.map (PreservesCokernel.iso F f).hom ≫ (PreservesCokernel.iso G (F.map f)).hom ≫
      (inducedCokernelIso F G H e f).hom =
    (e.app (cokernel f)).hom ≫ (PreservesCokernel.iso H f).hom := by
  apply (cancel_epi (G.map (F.map (cokernel.π f)))).mp
  calc
    _ = G.map (F.map (cokernel.π f) ≫ (PreservesCokernel.iso F f).hom) ≫
        (PreservesCokernel.iso G (F.map f)).hom ≫ (inducedCokernelIso F G H e f).hom := by
          rw [Functor.map_comp, Category.assoc]
    _ = (e.app B).hom ≫ cokernel.π (H.map f) := by
      rw [PreservesCokernel.π_iso_hom, PreservesCokernel.π_iso_hom_assoc, induced_π]
    _ = _ := by
      have hn : G.map (F.map (cokernel.π f)) ≫ (e.app (cokernel f)).hom =
          (e.app B).hom ≫ H.map (cokernel.π f) := e.hom.naturality (cokernel.π f)
      rw [← Category.assoc, hn, Category.assoc, PreservesCokernel.π_iso_hom]

end

end ManuscriptAudit.PreservedCokernelComposition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PreservedCokernelComposition.cokernelComparisons_compose
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun n => !allowed.contains n
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
