import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.KummerUnitsPresheaf

/-!
# The sheafified Kummer power map

On a small affine étale site, the power map on the sheafification of the
coordinate-unit presheaf is an epimorphism when its positive degree is
invertible. This yields a short exact sequence with its categorical kernel.
-/

namespace ManuscriptAudit.KummerSheafSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KummerUnitsPresheaf

universe u

/-- Sheafification of the coordinate-unit presheaf. -/
noncomputable abbrev unitSheaf (X : Scheme.{u}) :=
  (presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}).obj (units X)

/-- The sheaf morphism obtained from the unit-power presheaf morphism. -/
noncomputable abbrev sheafPower (X : Scheme.{u}) (d : ℕ) :
    unitSheaf X ⟶ unitSheaf X :=
  (presheafToSheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}).map (power X d)

/-- The actual sheafified (d)-th power map is an epimorphism. -/
theorem sheafPower_epi (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) : Epi (sheafPower (Spec R) d) := by
  letI : Sheaf.IsLocallySurjective (sheafPower (Spec R) d) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff
      (Scheme.AffineEtale.topology (Spec R)) (power (Spec R) d)).mpr
      (power_isLocallySurjective_spec R d hpos hd)
  infer_instance

/-- The kernel sequence for the sheafified power map. -/
noncomputable def sequence (X : Scheme.{u}) (d : ℕ) :
    ShortComplex (Sheaf (Scheme.AffineEtale.topology X) AddCommGrpCat.{u}) :=
  ShortComplex.mk (kernel.ι (sheafPower X d)) (sheafPower X d)
    (kernel.condition (sheafPower X d))

/-- The kernel sequence is short exact on the small affine étale site. -/
theorem sequence_shortExact (R : CommRingCat.{u}) (d : ℕ) (hpos : 0 < d)
    (hd : IsUnit (d : R)) : (sequence (Spec R) d).ShortExact := by
  letI : Epi (sheafPower (Spec R) d) := sheafPower_epi R d hpos hd
  apply ShortComplex.ShortExact.mk'
  · exact ShortComplex.exact_kernel (sheafPower (Spec R) d)
  · change Mono (kernel.ι (sheafPower (Spec R) d))
    infer_instance
  · change Epi (sheafPower (Spec R) d)
    infer_instance

end ManuscriptAudit.KummerSheafSequence

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerSheafSequence.sheafPower_epi,
      ``ManuscriptAudit.KummerSheafSequence.sequence_shortExact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
