import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.KummerRelativeCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerKernel
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitSheaf

/-! The full native small étale Kummer sequence over an arbitrary scheme
with a morphism to an algebraically closed coefficient field. -/

namespace ManuscriptAudit.KummerRelativeFull

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open KummerUnitsPresheaf KummerSheafSequence
open KummerConstantCoefficients (coefficientGroup)
open KummerRelativeCoefficients (coefficientMap)
open KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {X : Scheme.{0}} (k : X ⟶ Spec (CommRingCat.of K))

private abbrev C := AddCommGrpCat.{0}
private abbrev A (X : Scheme.{0}) := Scheme.AffineEtale.topology X
private abbrev J (X : Scheme.{0}) := X.smallEtaleTopology
private abbrev E (X : Scheme.{0}) := Scheme.AffineEtale.sheafEquiv X C

include k in
private theorem affine_power_epi (d : ℕ) (hpos : 0 < d) [NeZero (d : K)] :
    Epi (sheafPower X d) := by
  have h : Presheaf.IsLocallySurjective (A X) (power X d) := by
    apply power_isLocallySurjective d hpos
    intro U
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (coefficientMap k U)
  letI : Sheaf.IsLocallySurjective (sheafPower X d) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff (A X) (power X d)).mpr h
  infer_instance

include k in
private theorem affine_shortExact (d : ℕ) (hpos : 0 < d) [NeZero (d : K)] :
    (KummerSheafSequence.sequence X d).ShortExact := by
  letI := affine_power_epi k d hpos
  exact ShortComplex.ShortExact.mk' (ShortComplex.exact_kernel (sheafPower X d))
    (inferInstanceAs (Mono (kernel.ι (sheafPower X d)))) (inferInstanceAs (Epi (sheafPower X d)))

/-- Full Kummer short complex via the actual equivalence with the affine basis. -/
def sequence (X : Scheme.{0}) (d : ℕ) :
    ShortComplex (Sheaf (J X) C) :=
  (KummerSheafSequence.sequence X d).map (E X).functor

include k in
/-- The full Kummer sequence is geometrically exact. -/
theorem sequence_shortExact (d : ℕ) (hpos : 0 < d) [NeZero (d : K)] :
    (sequence X d).ShortExact := by
  let P := (E X).functor
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  exact (affine_shortExact k d hpos).map_of_exact P

private def affineConstantIso (M : C) :
    (constantSheaf (A X) C).obj M ≅ (E X).inverse.obj ((constantSheaf (J X) C).obj M) := by
  let G := Scheme.AffineEtale.Spec X
  let e := Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (A X) (J X) G C
  exact e.app ((Functor.const (X.Etaleᵒᵖ)).obj M)

/-- The first term is the actual constant sheaf of coefficient roots. -/
def firstIso {d : ℕ} [NeZero d] [NeZero (d : K)] [HasEnoughRootsOfUnity K d] :
    (constantSheaf (J X) C).obj (coefficientGroup K d) ≅ (sequence X d).X₁ :=
  ((E X).counitIso.app _).symm ≪≫
    (E X).functor.mapIso ((affineConstantIso (X := X) (coefficientGroup K d)).symm ≪≫
      KummerRelativeCoefficients.constantRootSheafIso (d := d) k ≪≫
      KummerKernel.sheafifiedRootsIsoKernel X d)

private def affineUnitsIso :
    (E X).inverse.obj (fullCoordinateUnitSheaf X) ≅ unitSheaf X := by
  let F := (E X).inverse.obj (fullCoordinateUnitSheaf X)
  let U := KummerUnitsSheaf.coordinateUnitSheaf X
  have e : F.obj ≅ U.obj := by
    change (Scheme.AffineEtale.Spec X).op ⋙ fullCoordinateUnits X ≅
      KummerUnitsPresheaf.units X
    exact affineRestrictionUnitsIso X
  have e' : F ≅ U := (fullyFaithfulSheafToPresheaf (A X) C).preimageIso e
  exact e' ≪≫ KummerUnitsSheaf.coordinateUnitSheafIso X

/-- The two unit terms are the actual full-site coordinate-unit sheaf. -/
def unitsIso (d : ℕ) : fullCoordinateUnitSheaf X ≅ (sequence X d).X₂ :=
  ((E X).counitIso.app _).symm ≪≫ (E X).functor.mapIso (affineUnitsIso (X := X))

private theorem affine_power_nsmul (d : ℕ) :
    sheafPower X d = d • 𝟙 (unitSheaf X) := by
  let P := presheafToSheaf (A X) C
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  have h : power X d = d • 𝟙 (units X) := by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.ext
    intro a
    rfl
  change P.map (power X d) = d • 𝟙 (P.obj (units X))
  rw [h, Functor.map_nsmul, P.map_id]

/-- The full sequence's last arrow acts by the usual coordinate power. -/
theorem power_nsmul (d : ℕ) : (sequence X d).g = d • 𝟙 (sequence X d).X₂ := by
  let P := (E X).functor
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  change P.map (sheafPower X d) = d • 𝟙 (P.obj (unitSheaf X))
  rw [affine_power_nsmul, Functor.map_nsmul, P.map_id]

end
end ManuscriptAudit.KummerRelativeFull

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.KummerRelativeFull.sequence_shortExact,
      ``ManuscriptAudit.KummerRelativeFull.firstIso,
      ``ManuscriptAudit.KummerRelativeFull.unitsIso,
      ``ManuscriptAudit.KummerRelativeFull.power_nsmul] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
