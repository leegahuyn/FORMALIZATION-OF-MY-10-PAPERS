import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.ShortComplex.Exact
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorHom
import PrimalitySheafVerification.ManuscriptAudit.DenseSheafKernel
import PrimalitySheafVerification.ManuscriptAudit.GenericEtaleUnitQuotient

/-!
# The divisor kernel on the small affine étale site

The actual regular-to-generic unit map identifies the kernel of the
divisor. It suffices to check this on the dense subsite of integral
affine charts, where the kernel is given by the Dedekind divisor theorem.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K F : Type) [Field K] [IsAlgClosed K] [Field F]
  [Algebra (Polynomial K) F] [IsFractionRing (Polynomial K) F]

private abbrev A := Polynomial K
private abbrev E := Scheme.AffineEtale.sheafEquiv (X K) AddCommGrpCat.{0}
private abbrev T := Scheme.AffineEtale.topology (X K)
private abbrev I := AffineEtaleDomainSite.inclusion (A K)
private abbrev P := ((E K).inverse.obj (KummerUnitsSheaf.fullCoordinateUnitSheaf (X K))).obj
private abbrev G := ((E K).inverse.obj (genericUnitImage (A K) F)).obj
private abbrev D := (affineDivisorSheaf K).obj

/-- The restriction of the actual regular-to-generic unit morphism. -/
abbrev affineRegularUnitsHom := (E K).inverse.map (genericPointUnitsHom (A K) F)

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
    (U : (AffineEtaleDomainSite.integralCharts (A K)).FullSubcategory) :
    Function.Exact ((affineRegularUnitsHom K F).hom.app (op U.obj)).hom
      ((affineDivisorHom K F).hom.app (op U.obj)).hom := by
  let B := coordinateRing K U.obj
  letI := coordinateAlgebra K U.obj
  letI := coordinateAlgebra_etale K U.obj
  letI : IsDomain B := U.property
  let V := chartObject K B
  let e := coordinateChartIso K U.obj U.property
  let r := (affineRegularUnitsHom K F).hom
  let d := (affineDivisorHom K F).hom
  let q := chartDivisorMap K B F
  let eP := ((P K).mapIso e.op).addCommGroupIsoToAddEquiv
  let eG := ((G K F).mapIso e.op).addCommGroupIsoToAddEquiv
  let eD := ((D K).mapIso e.op).addCommGroupIsoToAddEquiv
  have hR (x : (P K).obj (op U.obj)) :
      eG (r.app (op U.obj) x) = r.app (op V) (eP x) :=
    (ConcreteCategory.congr_hom (r.naturality e.hom.op) x).symm
  have hd : d.app (op U.obj) =
      (G K F).map e.hom.op ≫ AddCommGrpCat.ofHom q ≫ (D K).map e.inv.op :=
    affineDivisorHom_app_integral K F U
  have hD (x : (G K F).obj (op U.obj)) :
      eD (d.app (op U.obj) x) = q (eG x) := by
    rw [hd]
    change (D K).map e.hom.op ((D K).map e.inv.op (q (eG x))) = _
    exact eD.apply_symm_apply (q (eG x))
  have hChart : Function.Exact (r.app (op V)).hom q := chartDivisorMap_exact K B F
  exact exact_transport (r.app (op U.obj)).hom (d.app (op U.obj)).hom
    (r.app (op V)).hom q eP.toEquiv eG.toEquiv eD.toEquiv eD.map_zero hR hD hChart

/-- Regular units have zero divisor on the full affine étale site. -/
theorem affineRegularUnits_comp_divisor :
    affineRegularUnitsHom K F ≫ affineDivisorHom K F = 0 := by
  letI : (I K).IsCoverDense (T K) :=
    AffineEtaleDomainSite.integralCharts_coverDense (A K)
  apply DenseSheafKernel.hom_ext (T K) (I K)
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  let m := (affineRegularUnitsHom K F).hom.app (op (unop U).obj)
  change (affineDivisorHom K F).hom.app (op (unop U).obj) (m x) = 0
  exact (affineUnits_exact_onIntegral K F (unop U) (m x)).mpr ⟨x, rfl⟩

/-- The actual regular, generic, and divisor sheaves form a short complex
on the affine étale site. -/
def affineDivisorSequence : ShortComplex (Sheaf (T K) AddCommGrpCat.{0}) :=
  ShortComplex.mk (affineRegularUnitsHom K F) (affineDivisorHom K F)
    (affineRegularUnits_comp_divisor K F)

/-- The actual regular units realize the kernel of the divisor morphism on
the affine étale site. -/
def affineDivisorSequence_isLimit :
    IsLimit (KernelFork.ofι (affineDivisorSequence K F).f (affineDivisorSequence K F).zero) := by
  letI : (I K).IsCoverDense (T K) :=
    AffineEtaleDomainSite.integralCharts_coverDense (A K)
  letI : Mono (genericPointUnitsHom (A K) F) := genericPointUnitsHom_mono (A K) F
  letI : Mono (affineRegularUnitsHom K F) := inferInstance
  refine DenseSheafKernel.isLimit (T K) (I K) (affineRegularUnitsHom K F)
    (affineDivisorHom K F) (affineRegularUnits_comp_divisor K F) ?_ ?_
  · intro U
    let g := (affineRegularUnitsHom K F).hom.app (op (unop U).obj)
    exact (AddCommGrpCat.mono_iff_injective g).mp
      (genericPointUnitsHom_onAffineSite_mono (A K) F (unop U).obj)
  · intro U
    exact affineUnits_exact_onIntegral K F (unop U)

/-- The actual divisor sequence is exact on the affine étale site. -/
theorem affineDivisorSequence_exact : (affineDivisorSequence K F).Exact :=
  (affineDivisorSequence K F).exact_of_f_is_kernel (affineDivisorSequence_isLimit K F)

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineLineDivisorSheaf.affineUnits_exact_onIntegral,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisorSequence_isLimit,
      ``ManuscriptAudit.AffineLineDivisorSheaf.affineDivisorSequence_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
