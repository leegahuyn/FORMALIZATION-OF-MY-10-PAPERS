import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import PrimalitySheafVerification.ManuscriptAudit.KummerSheafSequence

/-!
# Native low-degree Kummer cohomology sequence

The short exact sequence for the sheafified power map gives an exact
sequence in Mathlib's derived sheaf cohomology. Its coefficient object
here is the categorical kernel of the power map.
-/

namespace ManuscriptAudit.KummerCohomologySequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open KummerSheafSequence

universe u

private noncomputable abbrev site (R : CommRingCat.{u}) := Scheme.AffineEtale.topology (Spec R)

/-- The small affine étale abelian sheaf category has Ext in the coefficient universe. -/
theorem affineSiteHasExt (R : CommRingCat.{u}) :
    HasExt.{u} (Sheaf (site R) AddCommGrpCat.{u}) := by
  let C := Sheaf (site R) AddCommGrpCat.{u}
  letI : IsGrothendieckAbelian.{u} C :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology (Spec R) AddCommGrpCat.{u}
  letI : LocallySmall.{u} C := IsGrothendieckAbelian.locallySmall (C := C)
  letI : EnoughInjectives C := IsGrothendieckAbelian.enoughInjectives.{u} (C := C)
  exact hasExt_of_enoughInjectives C

attribute [local instance] affineSiteHasExt

private noncomputable abbrev integerConstant (R : CommRingCat.{u}) :
    Sheaf (site R) AddCommGrpCat.{u} :=
  (constantSheaf (site R) AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

/-- The coefficient sheaf of the power-map kernel sequence. -/
noncomputable abbrev powerKernel (R : CommRingCat.{u}) (d : ℕ) :=
  kernel (sheafPower (Spec R) d)

/-- The connecting homomorphism from degree zero to degree one. -/
noncomputable def connecting (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) : Sheaf.H (unitSheaf (Spec R)) 0 →+ Sheaf.H (powerKernel R d) 1 :=
  (sequence_shortExact R d hpos hd).extClass.postcomp (integerConstant R)
    (show 0 + 1 = 1 by rfl)

/-- Exactness at the target of the power map in degree zero. -/
theorem degree_zero_exact (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) :
    Function.Exact (Sheaf.H.map (sheafPower (Spec R) d) 0)
      (connecting R d hpos hd) := by
  have h := Ext.covariant_sequence_exact₃' (integerConstant R)
    (sequence_shortExact R d hpos hd) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- Exactness at the kernel coefficient sheaf in degree one. -/
theorem degree_one_exact (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) :
    Function.Exact (connecting R d hpos hd)
      (Sheaf.H.map (kernel.ι (sheafPower (Spec R) d)) 1) := by
  have h := Ext.covariant_sequence_exact₁' (integerConstant R)
    (sequence_shortExact R d hpos hd) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  exact h

/-- The full six-term sequence across degrees zero and one. -/
noncomputable def sixTermSequence (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) : ComposableArrows AddCommGrpCat.{u} 5 :=
  Ext.covariantSequence (integerConstant R) (sequence_shortExact R d hpos hd) 0 1 rfl

theorem sixTermSequence_exact (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) : (sixTermSequence R d hpos hd).Exact :=
  Ext.covariantSequence_exact (integerConstant R) (sequence_shortExact R d hpos hd) 0 1 rfl

end ManuscriptAudit.KummerCohomologySequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerCohomologySequence.degree_zero_exact,
      ``ManuscriptAudit.KummerCohomologySequence.degree_one_exact,
      ``ManuscriptAudit.KummerCohomologySequence.sixTermSequence_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
