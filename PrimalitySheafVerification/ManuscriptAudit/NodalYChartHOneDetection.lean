import Lean.Util.CollectAxioms
import Mathlib.RingTheory.Localization.Ideal
import PrimalitySheafVerification.ManuscriptAudit.NodalProjectiveHOneRestriction
import PrimalitySheafVerification.ManuscriptAudit.NodalSmoothLocusGm

/-! The actual smooth node is detected in degree one upon restriction to its
Y-chart, by comparing the genuine site arrow to a Laurent principal open. -/

namespace ManuscriptAudit.NodalYChartHOneDetection

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open NodalProjectiveClosure (projectiveNode projectiveNodeToBase)
open NodalSmoothLocusOverlap (smoothOpen ySmooth ySmooth_ambient)
open NodalSmoothLocusGm (smoothLocusIsoGm ySmooth_comp_iso yChartIsoPrincipal yChartIsoPrincipal_comp)
open NodalProperYChart (chartOpen)
open NodalSmoothMobiusGm (Gm laurentRing)
open NodalSmoothMobiusY (plusRing plusInGm uPlusOne)
open NodalProjectiveHOneRestriction (primitiveNegOne rootLabelIso)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3500

attribute [local instance] GeometricSkyscraperCohomology.etaleSiteHasExt

variable (K : Type) [Field K]

private abbrev C := AddCommGrpCat.{0}
private abbrev M := AddCommGrpCat.of (ZMod 2)
private abbrev X := projectiveNode K
private abbrev J := (X K).smallEtaleTopology
private abbrev F := (constantSheaf (J K) C).obj M

private theorem laurent_denominator_good :
    Submonoid.powers (Polynomial.X : Polynomial K) ≤ (Polynomial K)⁰ := by
  rintro _ ⟨n, rfl⟩
  exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n Polynomial.X_ne_zero)

private instance laurentDomain : IsDomain (laurentRing K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (laurentRing K) (laurent_denominator_good K)

private instance laurentPID : IsPrincipalIdealRing (laurentRing K) := ⟨fun I => by
  rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : Polynomial K)) (laurentRing K) I]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (laurentRing K))
    (inferInstance : (I.under (Polynomial K)).IsPrincipal)⟩

private theorem plus_ne_zero : uPlusOne K ≠ 0 := by
  have hX : (Polynomial.X : Polynomial K) + 1 ≠ 0 := by
    intro h
    have he := congrArg (Polynomial.eval (0 : K)) h
    exact (one_ne_zero : (1 : K) ≠ 0) (by simpa using he)
  intro h
  apply hX
  exact (IsLocalization.to_map_eq_zero_iff (M := Submonoid.powers (Polynomial.X : Polynomial K))
    (laurentRing K) (laurent_denominator_good K)).mp h

abbrev smoothObject : (X K).Etale := Scheme.Etale.mk (smoothOpen K).ι
abbrev yObject : (X K).Etale := Scheme.Etale.mk (chartOpen K)

/-- The actual chart arrow into the smooth locus on the ambient small étale site. -/
def yIntoSmooth : yObject K ⟶ smoothObject K :=
  MorphismProperty.Over.homMk (ySmooth K) (ySmooth_ambient K)

private abbrev locHom : CommRingCat.of (laurentRing K) ⟶ CommRingCat.of (plusRing K) :=
  CommRingCat.ofHom (algebraMap (laurentRing K) (plusRing K))

private instance locOpen : IsOpenImmersion (plusInGm K) :=
  IsOpenImmersion.of_isLocalization (S := plusRing K) (uPlusOne K)

set_option maxHeartbeats 1000000 in
private theorem roots_restriction_injective (h2 : (2 : K) ≠ 0) :
    let G := (constantSheaf (J K) C).obj (KummerConstantCoefficients.coefficientGroup K 2)
    Function.Injective ((G.cohomologyPresheaf 1).map (yIntoSmooth K).op) := by
  letI : NeZero ((2 : ℕ) : K) := ⟨by simpa using h2⟩
  letI : HasEnoughRootsOfUnity K 2 :=
    { prim := ⟨-1, primitiveNegOne K h2⟩, cyc := rootsOfUnity.isCyclic K 2 }
  let G := (constantSheaf (J K) C).obj (KummerConstantCoefficients.coefficientGroup K 2)
  let P := G.cohomologyPresheaf 1
  let s := (smoothOpen K).ι
  let p := plusInGm K
  let E := smoothLocusIsoGm K h2
  let Q := yChartIsoPrincipal K h2
  let j : Gm K ⟶ X K := E.inv ≫ s
  letI : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hS : E.hom ≫ j = s := by simp [j]
  have hQ : Q.hom ≫ (p ≫ j) = chartOpen K := by
    calc
      _ = NodalSmoothLocusGm.yGm K h2 ≫ j := by
        rw [← Category.assoc]
        exact congrArg (fun f => f ≫ j) (yChartIsoPrincipal_comp K h2)
      _ = ySmooth K ≫ s := by
        rw [← ySmooth_comp_iso, Category.assoc, hS]
      _ = _ := ySmooth_ambient K
  let eS : smoothObject K ≅ Scheme.Etale.mk j :=
    MorphismProperty.Over.isoMk E hS
  let eY : yObject K ≅ Scheme.Etale.mk (p ≫ j) :=
    MorphismProperty.Over.isoMk Q hQ
  let a := yIntoSmooth K
  let b := KummerRelativeUnitSections.chartArrow (locHom K) j
  have hab : a ≫ eS.hom = eY.hom ≫ b := by
    apply MorphismProperty.Over.Hom.ext
    change ySmooth K ≫ E.hom = Q.hom ≫ p
    exact (ySmooth_comp_iso K h2).trans (yChartIsoPrincipal_comp K h2).symm
  have hi : b ≫ eS.inv = eY.inv ≫ a := by
    apply (cancel_mono eS.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, hab, Iso.inv_hom_id_assoc]
  have hm : P.map eS.inv.op ≫ P.map b.op = P.map a.op ≫ P.map eY.inv.op := by
    rw [← P.map_comp, ← P.map_comp, ← op_comp, ← op_comp, hi]
  have hb : Function.Injective (P.map b.op) :=
    KummerPrincipalOpenRestriction.restriction_constant_injective (projectiveNodeToBase K)
      j (uPlusOne K) (plus_ne_zero K) 2 (by decide)
  change Function.Injective (P.map a.op)
  intro x y h
  apply (P.mapIso eS.symm.op).addCommGroupIsoToAddEquiv.injective
  apply hb
  have hx := ConcreteCategory.congr_hom hm x
  have hy := ConcreteCategory.congr_hom hm y
  exact hx.trans ((congrArg (P.map eY.inv.op) h).trans hy.symm)

/-- Actual restriction from the smooth locus to its Y-chart is injective on H¹. -/
theorem restriction_injective (h2 : (2 : K) ≠ 0) :
    Function.Injective (((F K).cohomologyPresheaf 1).map (yIntoSmooth K).op) := by
  let a := yIntoSmooth K
  let Q := (Sheaf.cohomologyPresheafFunctor (J K) 1).mapIso
    ((constantSheaf (J K) C).mapIso (rootLabelIso K h2).symm)
  have hG := roots_restriction_injective K h2
  intro x y h
  apply (Q.app (op (smoothObject K))).addCommGroupIsoToAddEquiv.injective
  apply hG
  have hx := ConcreteCategory.congr_hom (Q.hom.naturality a.op) x
  have hy := ConcreteCategory.congr_hom (Q.hom.naturality a.op) y
  exact hx.symm.trans ((congrArg (Q.hom.app (op (yObject K))) h).trans hy)

end
end ManuscriptAudit.NodalYChartHOneDetection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.NodalYChartHOneDetection.restriction_injective
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
