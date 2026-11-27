import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerTorsionFree

/-! The native Kummer boundary of actual global units, with its kernel
of power multiples and its exact first-cohomology surjectivity criterion. -/

namespace ManuscriptAudit.ProetaleKummerBoundaryNative

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleKummerPower (J G power)
open ProetaleKummerSequence (sequence_shortExact constantKernelIso)
open ProetaleKummerCoefficientMap (coefficientGroup)
open ProetaleKummerTorsionFree (map_power_apply)
open ProetaleUnitSheaf (unitSheaf)
open ProetaleCohomologyIso (cohomologyIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {K : Type} [Field K] (k : X ⟶ Spec (CommRingCat.of K))
  (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d]

private abbrev integers := (constantSheaf (J X) G).obj (AddCommGrpCat.of (ULift.{1} ℤ))
private abbrev delta : Sheaf.H (unitSheaf X) 0 →+ Sheaf.H (kernel (power X d)) 1 :=
  (sequence_shortExact k d).extClass.postcomp (integers (X := X)) (show 0 + 1 = 1 by rfl)

private abbrev e := cohomologyIso (X := X) (constantKernelIso k d) 1

/-- The boundary of the actual native Kummer short exact sequence. -/
def unitBoundary : Sheaf.H (unitSheaf X) 0 →+
    Sheaf.H ((constantSheaf (J X) G).obj (coefficientGroup K d)) 1 :=
  (e k d).symm.toAddMonoidHom.comp (delta k d)

theorem unitBoundary_eq_zero_iff (a : Sheaf.H (unitSheaf X) 0) :
    unitBoundary k d a = 0 ↔ ∃ c : Sheaf.H (unitSheaf X) 0, d • c = a := by
  have hu : unitBoundary k d a = 0 ↔ delta k d a = 0 := by
    change (e k d).symm (delta k d a) = 0 ↔ _
    constructor
    · intro h
      exact (e k d).symm.injective (h.trans (map_zero (e k d).symm).symm)
    · intro h
      exact (congrArg (e k d).symm h).trans (map_zero (e k d).symm)
  rw [hu]
  have h := Ext.covariant_sequence_exact₃' (integers (X := X)) (sequence_shortExact k d) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  have hex : Function.Exact (Sheaf.H.map (power X d) 0) (delta k d) := h
  rw [hex a]
  simp only [map_power_apply]

theorem unitBoundary_surjective
    (hHOne : Subsingleton (Sheaf.H (unitSheaf X) 1)) :
    Function.Surjective (unitBoundary k d) := by
  intro x
  have hx : Sheaf.H.map (kernel.ι (power X d)) 1 ((e k d) x) = 0 := hHOne.elim _ _
  obtain ⟨a, ha⟩ := Ext.covariant_sequence_exact₁ (integers (X := X))
    (sequence_shortExact k d) ((e k d) x) hx rfl
  refine ⟨a, ?_⟩
  change (e k d).symm (delta k d a) = x
  have h : delta k d a = e k d x := ha
  rw [h, AddEquiv.symm_apply_apply]

end
end ManuscriptAudit.ProetaleKummerBoundaryNative

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleKummerBoundaryNative.unitBoundary_eq_zero_iff,
      ``ManuscriptAudit.ProetaleKummerBoundaryNative.unitBoundary_surjective] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
