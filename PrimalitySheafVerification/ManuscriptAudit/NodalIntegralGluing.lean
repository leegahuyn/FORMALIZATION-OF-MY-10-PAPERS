import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Basis
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import PrimalitySheafVerification.ManuscriptAudit.NodalIntegralChartTransition
import PrimalitySheafVerification.ManuscriptAudit.NodalYChartAlgebra

/-! Gluing the two literal affine charts and their transition gives a
flat finite-type nodal model over the coefficient scheme. -/

namespace ManuscriptAudit.NodalIntegralGluing

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open NodalIntegralChartTransition
open Polynomial

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u
variable (R : Type u) [CommRing R]

abbrev zScheme := Spec (CommRingCat.of (zChart R))
abbrev yScheme := Spec (CommRingCat.of (yChart R))
abbrev overlapScheme := Spec (CommRingCat.of (zOverlap R))
abbrev base := Spec (CommRingCat.of R)

def overlapToZ : overlapScheme R ⟶ zScheme R :=
  Spec.map (CommRingCat.ofHom (algebraMap (zChart R) (zOverlap R)))

def overlapToY : overlapScheme R ⟶ yScheme R :=
  (Scheme.Spec.mapIso (transition R).symm.toCommRingCatIso.op).hom ≫
    Spec.map (CommRingCat.ofHom (algebraMap (yChart R) (yOverlap R)))

instance : IsOpenImmersion (overlapToZ R) :=
  IsOpenImmersion.of_isLocalization (S := zOverlap R) (yZ R)

instance : IsOpenImmersion (overlapToY R) := by
  letI : IsOpenImmersion
      (Spec.map (CommRingCat.ofHom (algebraMap (yChart R) (yOverlap R)))) :=
    IsOpenImmersion.of_isLocalization (S := yOverlap R) (zY R)
  unfold overlapToY
  infer_instance

/-- The diagram for gluing the two charts on their common principal open. -/
def chartObj : Bool → Scheme.{u}
  | false => zScheme R
  | true => yScheme R

def overlapIn : ∀ b : Bool, overlapScheme R ⟶ chartObj R b
  | false => overlapToZ R
  | true => overlapToY R

abbrev diagram := WidePushoutShape.wideSpan (overlapScheme R) (chartObj R) (overlapIn R)

instance {i j : WidePushoutShape Bool} (f : i ⟶ j) :
    IsOpenImmersion ((diagram R).map f) := by
  cases f with
  | id i =>
    rw [WidePushoutShape.hom_id, Functor.map_id]
    infer_instance
  | init b =>
    cases b
    · exact inferInstanceAs (IsOpenImmersion (overlapToZ R))
    · exact inferInstanceAs (IsOpenImmersion (overlapToY R))

/-- The two affine pieces glued as actual schemes, with these prescribed coordinates. -/
abbrev model : Scheme.{u} := colimit (diagram R)

def chartIn (b : Bool) : chartObj R b ⟶ model R :=
  colimit.ι (diagram R) (some b)

instance chartIn_open (b : Bool) : IsOpenImmersion (chartIn R b) := by
  unfold chartIn
  infer_instance

def chartToBase : ∀ b : Bool, chartObj R b ⟶ base R
  | false => Spec.map (CommRingCat.ofHom (algebraMap R (zChart R)))
  | true => Spec.map (CommRingCat.ofHom (algebraMap R (yChart R)))

def overlapToBase : overlapScheme R ⟶ base R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (zOverlap R)))

theorem overlapToZ_over : overlapToZ R ≫ chartToBase R false = overlapToBase R := by
  unfold overlapToZ chartToBase overlapToBase
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (IsScalarTower.algebraMap_eq R (zChart R) (zOverlap R)).symm

theorem overlapToY_over : overlapToY R ≫ chartToBase R true = overlapToBase R := by
  unfold overlapToY chartToBase overlapToBase
  rw [Category.assoc, ← Spec.map_comp]
  let e := (transition R).symm
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom
      ((algebraMap (yChart R) (yOverlap R)).comp (algebraMap R (yChart R)))) = _
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  change e (((algebraMap (yChart R) (yOverlap R)).comp (algebraMap R (yChart R))) a) = _
  rw [← IsScalarTower.algebraMap_eq R (yChart R) (yOverlap R)]
  exact e.commutes a

def baseCocone : Cocone (diagram R) :=
  WidePushoutShape.mkCocone (overlapToBase R) (chartToBase R) (by
    intro b
    cases b
    · exact overlapToZ_over R
    · exact overlapToY_over R)

/-- The glued node over the coefficient scheme. -/
def toBase : model R ⟶ base R := colimit.desc (diagram R) (baseCocone R)

theorem chartIn_over (b : Bool) : chartIn R b ≫ toBase R = chartToBase R b :=
  colimit.ι_desc (baseCocone R) (some b)

theorem overlap_over : colimit.ι (diagram R) none ≫ toBase R = overlapToBase R :=
  colimit.ι_desc (baseCocone R) none

private theorem zChart_flat : Flat (chartToBase R false) := by
  letI : Module.Free R (Polynomial R) := Module.Free.of_basis (Polynomial.basisMonomials R)
  have hmonic : (zEquation R).Monic := monic_X_pow_sub_C _ (n := 2) (by decide)
  letI : Module.Free (Polynomial R) (zChart R) := hmonic.free_adjoinRoot
  have hm := Module.Flat.trans R (Polynomial R) (zChart R)
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hm)

private def localizedYEquiv :
    yChart R ≃ₐ[R] Localization.Away ((1 : Polynomial R) - X ^ 2) := by
  simpa only [NodalYChartAlgebra.nodalYEquation R, yEquation] using
    (NodalYChartAlgebra.nodalYChartEquiv R).restrictScalars R

private theorem yChart_flat : Flat (chartToBase R true) := by
  let L := Localization.Away ((1 : Polynomial R) - X ^ 2)
  letI : Module.Free R (Polynomial R) := Module.Free.of_basis (Polynomial.basisMonomials R)
  letI : Module.Flat (Polynomial R) L := inferInstance
  letI : Module.Flat R L := Module.Flat.trans R (Polynomial R) L
  have hm : Module.Flat R (yChart R) :=
    Module.Flat.of_linearEquiv (localizedYEquiv R).toLinearEquiv
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr hm)

/-- This actual glued scheme is flat over its coefficient scheme. -/
theorem model_flat : Flat (toBase R) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (Scheme.IsLocallyDirected.openCover (diagram R))).mpr
  intro i
  rw [Scheme.IsLocallyDirected.openCover_f]
  cases i with
  | none =>
    rw [overlap_over, ← overlapToZ_over R]
    letI : Flat (chartToBase R false) := zChart_flat R
    infer_instance
  | some b =>
    change Flat (chartIn R b ≫ toBase R)
    rw [chartIn_over]
    cases b
    · exact zChart_flat R
    · exact yChart_flat R

private theorem zChart_finitePresentation :
    LocallyOfFinitePresentation (chartToBase R false) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr
    (inferInstanceAs (Algebra.FinitePresentation R (zChart R)))

private theorem yChart_finitePresentation :
    LocallyOfFinitePresentation (chartToBase R true) := by
  apply (LocallyOfFinitePresentation.SpecMap_iff _).mpr
  exact RingHom.finitePresentation_algebraMap.mpr
    (inferInstanceAs (Algebra.FinitePresentation R (yChart R)))

/-- The nodal model is locally of finite presentation. -/
theorem model_locallyOfFinitePresentation : LocallyOfFinitePresentation (toBase R) := by
  apply (IsZariskiLocalAtSource.iff_of_openCover
    (Scheme.IsLocallyDirected.openCover (diagram R))).mpr
  intro i
  rw [Scheme.IsLocallyDirected.openCover_f]
  cases i with
  | none =>
    rw [overlap_over, ← overlapToZ_over R]
    letI : LocallyOfFinitePresentation (chartToBase R false) := zChart_finitePresentation R
    infer_instance
  | some b =>
    change LocallyOfFinitePresentation (chartIn R b ≫ toBase R)
    rw [chartIn_over]
    cases b
    · exact zChart_finitePresentation R
    · exact yChart_finitePresentation R

/-- The model has two affine charts and is of finite type over the base. -/
theorem model_finiteType :
    LocallyOfFiniteType (toBase R) ∧ QuasiCompact (toBase R) := by
  letI : LocallyOfFinitePresentation (toBase R) := model_locallyOfFinitePresentation R
  let cov := Scheme.IsLocallyDirected.openCover (diagram R)
  letI : Finite cov.I₀ := inferInstanceAs (Finite (Option Bool))
  letI : ∀ i, CompactSpace (cov.X i) := fun i => by
    change CompactSpace ((diagram R).obj i)
    cases i with
    | none => exact inferInstanceAs (CompactSpace (overlapScheme R))
    | some b =>
      cases b
      · exact inferInstanceAs (CompactSpace (zScheme R))
      · exact inferInstanceAs (CompactSpace (yScheme R))
  letI : CompactSpace (model R) := cov.compactSpace
  exact ⟨inferInstance, quasiCompact_of_compactSpace _⟩

end
end ManuscriptAudit.NodalIntegralGluing

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.NodalIntegralGluing.chartIn_over,
      ``ManuscriptAudit.NodalIntegralGluing.model_flat,
      ``ManuscriptAudit.NodalIntegralGluing.model_locallyOfFinitePresentation,
      ``ManuscriptAudit.NodalIntegralGluing.model_finiteType] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
