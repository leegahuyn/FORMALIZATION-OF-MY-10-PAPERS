import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleKummerConstantTransition

/-! The constant sheaf of roots identifies the actual coefficient
transition with the actual categorical kernel transition. -/

namespace ManuscriptAudit.ProetaleKummerSheafTransition

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProetaleKummerPower (J G power)
open ProetaleKummerCoefficientMap (coefficientGroup constantToRoots)
open ProetaleKummerRoots (roots roots_isSheaf rootsKernelIso rootsKernelIso_hom_ι inclusion)
open ProetaleKummerSequence (constantKernelIso)
open ProetaleKummerKernelTransition (kernelTransition kernelTransition_ι)
open ProetaleKummerConstantTransition (coefficientTransition label label_transition)
open ProetaleUnitSheaf (unitSheaf)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

private abbrev constantPresheaf (d : ℕ) :=
  (Functor.const X.ProEtᵒᵖ).obj (coefficientGroup K d)

private abbrev toUnits (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d] :=
  ((constantKernelIso k d).hom ≫ kernel.ι (power X d)).hom

set_option maxHeartbeats 1200000 in
private theorem toSheafify_toUnits (d : ℕ) [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d] :
    toSheafify (J X) (constantPresheaf (K := K) (X := X) d) ≫ toUnits k d = label k d := by
  let η := constantToRoots k d
  let P := constantPresheaf (K := K) (X := X) d
  change toSheafify (J X) P ≫ sheafifyMap (J X) η ≫
    (isoSheafify (J X) (roots_isSheaf X d)).inv ≫
    (rootsKernelIso X d).hom.hom ≫ (kernel.ι (power X d)).hom = label k d
  rw [rootsKernelIso_hom_ι, ← Category.assoc (toSheafify (J X) P), ← toSheafify_naturality]
  simp only [Category.assoc, isoSheafify_inv, toSheafify_sheafifyLift_assoc, Category.id_comp, label, η]

variable (ℓ n : ℕ)

abbrev constantTransition :=
  (constantSheaf (J X) G).map (coefficientTransition K ℓ n)

set_option maxHeartbeats 1600000 in
/-- Constant roots and categorical kernels form the same finite coefficient tower. -/
theorem constantKernelIso_naturality
    [NeZero (ℓ ^ n)] [NeZero (ℓ ^ (n + 1))]
    [NeZero ((ℓ ^ n : ℕ) : K)] [NeZero ((ℓ ^ (n + 1) : ℕ) : K)]
    [HasEnoughRootsOfUnity K (ℓ ^ n)] [HasEnoughRootsOfUnity K (ℓ ^ (n + 1))] :
    constantTransition (K := K) (X := X) ℓ n ≫ (constantKernelIso k (ℓ ^ n)).hom =
      (constantKernelIso k (ℓ ^ (n + 1))).hom ≫ kernelTransition X ℓ n := by
  apply (cancel_mono (kernel.ι (power X (ℓ ^ n)))).mp
  simp only [Category.assoc, kernelTransition_ι]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (J X) _ _ (unitSheaf X).property
  let g := (Functor.const X.ProEtᵒᵖ).map (coefficientTransition K ℓ n)
  let P := constantPresheaf (K := K) (X := X) (ℓ ^ (n + 1))
  let Q := constantPresheaf (K := K) (X := X) (ℓ ^ n)
  change toSheafify (J X) P ≫ (sheafifyMap (J X) g ≫ toUnits k (ℓ ^ n)) =
    toSheafify (J X) P ≫ (toUnits k (ℓ ^ (n + 1)) ≫ (power X ℓ).hom)
  calc
    _ = g ≫ (toSheafify (J X) Q ≫ toUnits k (ℓ ^ n)) := by
      rw [← Category.assoc, ← toSheafify_naturality, Category.assoc]
    _ = g ≫ label k (ℓ ^ n) := by rw [toSheafify_toUnits]
    _ = label k (ℓ ^ (n + 1)) ≫ (power X ℓ).hom := label_transition ℓ n k
    _ = _ := by rw [← Category.assoc, toSheafify_toUnits]

end
end ManuscriptAudit.ProetaleKummerSheafTransition

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleKummerSheafTransition.constantKernelIso_naturality
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
