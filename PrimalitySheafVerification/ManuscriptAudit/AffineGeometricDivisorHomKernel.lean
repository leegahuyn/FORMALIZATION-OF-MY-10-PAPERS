import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Exact
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorHom
import PrimalitySheafVerification.ManuscriptAudit.DenseSheafKernel
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitQuotient

/-!
# The divisor kernel on the small affine étale site

The actual regular-to-generic unit map identifies the kernel of the
divisor. It suffices to check this on the dense subsite of integral
affine charts, where the kernel is given by the Dedekind divisor theorem.
-/

namespace ManuscriptAudit.AffineGeometricDivisorHomKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AffineGeometricDivisorSheaf AffineGeometricDivisorHom
open AffineGeometricDivisorSections AffineGeometricDivisorNaturality
open AffineGeometricIntegralChartCoordinates AffineGeometricChartDivisorMap
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K A F : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [Field F] [Algebra A F] [IsFractionRing A F]

private abbrev E := Scheme.AffineEtale.sheafEquiv (X A) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X A)
private abbrev I := AffineEtaleDomainSite.inclusion A
private abbrev P := ((E A).inverse.obj (KummerUnitsSheaf.fullCoordinateUnitSheaf (X A))).obj
private abbrev G := ((E A).inverse.obj (genericUnitImage A F)).obj
private abbrev D := (affineDivisorSheaf K A).obj

/-- The restriction of the actual regular-to-generic unit morphism. -/
abbrev affineRegularUnitsHom := (E A).inverse.map (genericPointUnitsHom A F)

private theorem exact_transport {M N L M' N' L' : Type*} [Zero L] [Zero L']
    (a : M → N) (b : N → L) (a' : M' → N') (b' : N' → L')
    (e₁ : M ≃ M') (e₂ : N ≃ N') (e₃ : L ≃ L') (hz : e₃ 0 = 0)
    (ha : ∀ x, e₂ (a x) = a' (e₁ x))
    (hb : ∀ x, e₃ (b x) = b' (e₂ x))
    (he : Function.Exact a' b') : Function.Exact a b := by
  intro x
  rw [← e₃.injective.eq_iff, hb, hz, he]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e₁.symm y, e₂.injective ?_⟩
    rw [ha, e₁.apply_symm_apply, hy]
  · rintro ⟨y, rfl⟩
    exact ⟨e₁ y, (ha y).symm⟩

set_option maxHeartbeats 2300000 in
/-- The actual affine sheaf sequence is exact on every integral affine chart. -/
theorem affineUnits_exact_onIntegral
    (U : (AffineEtaleDomainSite.integralCharts A).FullSubcategory) :
    Function.Exact ((affineRegularUnitsHom A F).hom.app (op U.obj)).hom
      ((affineDivisorHom K A F).hom.app (op U.obj)).hom := by
  let B := coordinateRing A U.obj
  letI := coordinateAlgebra A U.obj
  letI := coordinateAlgebra_etale A U.obj
  letI : IsDomain B := U.property
  let V := chartObject A B
  let e := coordinateChartIso A U.obj U.property
  let r := (affineRegularUnitsHom A F).hom
  let d := (affineDivisorHom K A F).hom
  let q := chartDivisorMap K A B F
  let eP := ((P A).mapIso e.op).addCommGroupIsoToAddEquiv
  let eG := ((G A F).mapIso e.op).addCommGroupIsoToAddEquiv
  let eD := ((D K A).mapIso e.op).addCommGroupIsoToAddEquiv
  have hR (x : (P A).obj (op U.obj)) :
      eG (r.app (op U.obj) x) = r.app (op V) (eP x) :=
    (ConcreteCategory.congr_hom (r.naturality e.hom.op) x).symm
  have hd : d.app (op U.obj) =
      (G A F).map e.hom.op ≫ AddCommGrpCat.ofHom q ≫ (D K A).map e.inv.op :=
    affineDivisorHom_app_integral K A F U
  have hD (x : (G A F).obj (op U.obj)) :
      eD (d.app (op U.obj) x) = q (eG x) := by
    rw [hd]
    change (D K A).map e.hom.op ((D K A).map e.inv.op (q (eG x))) = _
    exact eD.apply_symm_apply (q (eG x))
  have hChart : Function.Exact (r.app (op V)).hom q := chartDivisorMap_exact K A B F
  exact exact_transport (r.app (op U.obj)).hom (d.app (op U.obj)).hom
    (r.app (op V)).hom q eP.toEquiv eG.toEquiv eD.toEquiv eD.map_zero hR hD hChart

/-- Regular units have zero divisor on the full affine étale site. -/
theorem affineRegularUnits_comp_divisor :
    affineRegularUnitsHom A F ≫ affineDivisorHom K A F = 0 := by
  letI : (I A).IsCoverDense (T A) :=
    AffineEtaleDomainSite.integralCharts_coverDense A
  apply DenseSheafKernel.hom_ext (T A) (I A)
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  let m := (affineRegularUnitsHom A F).hom.app (op (unop U).obj)
  change (affineDivisorHom K A F).hom.app (op (unop U).obj) (m x) = 0
  exact (affineUnits_exact_onIntegral K A F (unop U) (m x)).mpr ⟨x, rfl⟩

/-- The actual regular, generic, and divisor sheaves form a short complex
on the affine étale site. -/
def affineDivisorSequence : ShortComplex (Sheaf (T A) AddCommGrpCat.{0}) :=
  ShortComplex.mk (affineRegularUnitsHom A F) (affineDivisorHom K A F)
    (affineRegularUnits_comp_divisor K A F)

/-- The actual regular units realize the kernel of the divisor morphism on
the affine étale site. -/
def affineDivisorSequence_isLimit :
    IsLimit (KernelFork.ofι (affineDivisorSequence K A F).f (affineDivisorSequence K A F).zero) := by
  letI : (I A).IsCoverDense (T A) :=
    AffineEtaleDomainSite.integralCharts_coverDense A
  letI : Mono (genericPointUnitsHom A F) := genericPointUnitsHom_mono A F
  letI : Mono (affineRegularUnitsHom A F) := inferInstance
  refine DenseSheafKernel.isLimit (T A) (I A) (affineRegularUnitsHom A F)
    (affineDivisorHom K A F) (affineRegularUnits_comp_divisor K A F) ?_ ?_
  · intro U
    let g := (affineRegularUnitsHom A F).hom.app (op (unop U).obj)
    exact (AddCommGrpCat.mono_iff_injective g).mp
      (genericPointUnitsHom_onAffineSite_mono A F (unop U).obj)
  · intro U
    exact affineUnits_exact_onIntegral K A F (unop U)

/-- The actual divisor sequence is exact on the affine étale site. -/
theorem affineDivisorSequence_exact : (affineDivisorSequence K A F).Exact :=
  (affineDivisorSequence K A F).exact_of_f_is_kernel (affineDivisorSequence_isLimit K A F)

end

end ManuscriptAudit.AffineGeometricDivisorHomKernel

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineGeometricDivisorHomKernel.affineUnits_exact_onIntegral,
      ``ManuscriptAudit.AffineGeometricDivisorHomKernel.affineDivisorSequence_isLimit,
      ``ManuscriptAudit.AffineGeometricDivisorHomKernel.affineDivisorSequence_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
