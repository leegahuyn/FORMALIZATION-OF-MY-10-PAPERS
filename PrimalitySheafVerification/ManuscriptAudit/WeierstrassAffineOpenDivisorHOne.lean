import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleUnitCohomology
import PrimalitySheafVerification.ManuscriptAudit.AffineOpenQuotientCycleNaturality
import PrimalitySheafVerification.ManuscriptAudit.DedekindCycleClass
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorConnectingAt
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassProjectiveGenericQuotient
import PrimalitySheafVerification.ManuscriptAudit.WeierstrassAffinePicard

/-! First unit cohomology on the actual affine Weierstrass open gives
the classical Dedekind ideal class of its genuine finite divisor cycle. -/

namespace ManuscriptAudit.WeierstrassAffineOpenDivisorHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite IsDedekindDomain
open WeierstrassProjectiveClosure WeierstrassProjectiveGenericPoint
open WeierstrassProjectiveGenericUnits WeierstrassProjectiveGenericQuotient
open AffineOpenQuotientCycleNaturality DedekindPrincipalDivisor DedekindCycleClass
open EtalePresheafHOneRepresentatives EtaleDivisorConnectingAt KummerUnitsSheaf

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable {K : Type} [Field K] [IsAlgClosed K] (W : WeierstrassCurve.Affine K) [W.IsElliptic]

private abbrev A := W.CoordinateRing
private abbrev F := W.FunctionField
private abbrev G := genericUnitImage W
private abbrev Q := quotient W
private abbrev i := regularToGeneric W
private abbrev j := affineOpen W
private abbrev f := genericPoint W
private abbrev U := Scheme.Etale.mk (j W)
private abbrev R := (G W).obj.obj (op (U W))
private abbrev D := (Q W).obj.obj (op (U W))

local instance : Mono (i W) := regularToGeneric_mono W
local instance : IsDedekindDomain (A W) := WeierstrassAffineDedekind.coordinateRing_isDedekindDomain W
local instance : Algebra.FiniteType K (A W) :=
  inferInstanceAs (Algebra.FiniteType K (AdjoinRoot W.polynomial))

private def cycle : D W ≃+ (HeightOneSpectrum (A W) →₀ ℤ) :=
  openQuotientCycle K (A W) (F W) (j W) (f W) rfl

private def value : R W ≃+ Additive (F W)ˣ :=
  openRationalValue (A W) (F W) (j W) (f W) rfl

private theorem cycle_projection (z : R W) :
    cycle W ((cokernel.π (i W)).hom.app (op (U W)) z) = principalDivisor (A W) (F W) (value W z) :=
  openQuotientCycle_projection K (A W) (F W) (j W) (f W) rfl z

private def mapClass : D W →+ Additive (ClassGroup (A W)) :=
  (cycleClass (A W) (F W)).comp (cycle W).toAddMonoidHom

private theorem mapClass_surjective : Function.Surjective (mapClass W) :=
  (cycleClass_surjective (A W) (F W)).comp (cycle W).surjective

private theorem mapClass_exact (d : D W) :
    connectingAt (i W) (U W) d = 0 ↔ mapClass W d = 0 := by
  rw [connectingAt_eq_zero_iff]
  change (∃ z : R W, _ = d) ↔ cycleClass (A W) (F W) (cycle W d) = 0
  rw [cycleClass_eq_zero]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨value W z, (cycle_projection W z).symm⟩
  · rintro ⟨u, hu⟩
    obtain ⟨z, rfl⟩ := (value W).surjective u
    exact ⟨z, (cycle W).injective ((cycle_projection W z).trans hu)⟩

private theorem genericHOne_zero : Subsingleton ((G W).H' 1 (U W)) :=
  AffineOpenDirectImageHOne.HOne_subsingleton (genericToAffine W) (j W) _
    (KummerUnitsSheaf.unitHOne_subsingleton_of_pid (F W))

/-- The actual first unit cohomology on the open right chart is the
usual Dedekind class group of its affine coordinate ring. -/
def affineHOneClassEquiv :
    (fullCoordinateUnitSheaf (projectiveScheme W)).H' 1 (U W) ≃+ Additive (ClassGroup (A W)) :=
  classEquiv (i W) (U W) (genericHOne_zero W) (mapClass W) (mapClass_surjective W) (mapClass_exact W)

/-- The actual affine open's unit cohomology is the geometric point group. -/
def affineHOnePointEquiv [DecidableEq K] :
    (fullCoordinateUnitSheaf (projectiveScheme W)).H' 1 (U W) ≃+ W.Point :=
  (affineHOneClassEquiv W).trans
    (((ClassGroup.equivPic (A W)).toAdditive).trans (WeierstrassAffinePicard.pointPicardEquiv W).symm)

end

end ManuscriptAudit.WeierstrassAffineOpenDivisorHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.WeierstrassAffineOpenDivisorHOne.affineHOneClassEquiv,
      ``ManuscriptAudit.WeierstrassAffineOpenDivisorHOne.affineHOnePointEquiv] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
