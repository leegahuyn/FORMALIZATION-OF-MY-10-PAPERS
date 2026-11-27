import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerTorsionFree

/-! The actual Kummer quotient identifies torsion in unit cohomology. -/

namespace ManuscriptAudit.ProetaleKummerTorsionExact

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleUnitSheaf (unitSheaf)
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (sequence_shortExact)
open ProetaleKummerTorsionFree (map_power_apply)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (d n : ℕ)

private abbrev integers :=
  (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))

abbrev unitTorsion :=
  (Sheaf.H.map (power X d) n).ker

theorem unitTorsion_mem_iff (a : Sheaf.H (unitSheaf X) n) :
    a ∈ unitTorsion X d n ↔ d • a = 0 := by
  change Sheaf.H.map (power X d) n a = 0 ↔ _
  rw [map_power_apply]

def rootsToTorsion :
    Sheaf.H (kernel (power X d)) n →+ unitTorsion X d n :=
  (Sheaf.H.map (kernel.ι (power X d)) n).codRestrict _ (by
    intro a
    change Sheaf.H.map (power X d) n (Sheaf.H.map (kernel.ι (power X d)) n a) = 0
    rw [← Sheaf.H.map_comp_apply, kernel.condition]
    simp [Sheaf.H.map_apply])

variable {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))
variable [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

include k in
theorem rootsToTorsion_surjective : Function.Surjective (rootsToTorsion X d n) := by
  intro a
  let hS := sequence_shortExact k d
  have ha : Sheaf.H.map (power X d) n a.val = 0 := a.property
  obtain ⟨b, hb⟩ := Ext.covariant_sequence_exact₂ (integers X) hS a.val ha
  exact ⟨b, Subtype.ext hb⟩

def boundary :
    Sheaf.H (unitSheaf X) n →+ Sheaf.H (kernel (power X d)) (n+1) :=
  (sequence_shortExact k d).extClass.postcomp (integers X) rfl

theorem boundary_range_eq_kernel :
    (boundary X d n k).range = (rootsToTorsion X d (n+1)).ker := by
  have h := Ext.covariant_sequence_exact₁' (integers X) (sequence_shortExact k d)
    n (n+1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  ext a
  have he : Function.Exact (boundary X d n k)
      (Sheaf.H.map (kernel.ι (power X d)) (n+1)) := h
  constructor
  · intro ha
    apply Subtype.ext
    exact (he a).2 ha
  · intro ha
    exact (he a).1 (congrArg Subtype.val ha)

end
end ManuscriptAudit.ProetaleKummerTorsionExact

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerTorsionExact.unitTorsion_mem_iff,
      ``ManuscriptAudit.ProetaleKummerTorsionExact.rootsToTorsion_surjective,
      ``ManuscriptAudit.ProetaleKummerTorsionExact.boundary_range_eq_kernel] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
