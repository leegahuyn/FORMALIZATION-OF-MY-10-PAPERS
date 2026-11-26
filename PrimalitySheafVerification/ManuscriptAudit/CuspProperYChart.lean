import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.CuspProperCompactification
import PrimalitySheafVerification.ManuscriptAudit.CuspYChartAlgebra

/-!
# The second affine chart of the proper cusp

The \(Y\ne0\) chart of the proper cusp is the line
\([X:Y:Z]=[s:1:s^3]\). To identify it with the actual schematic
closure of \([t^2:t^3:1]\), both parametrizations are restricted to
the common Laurent parameter \(t\), where \(s=t^{-1}\). The equality
is proved through the native overlap chart \(D_+(YZ)\). Dominance of
the Laurent parameter in each affine model then identifies their
schematic-image ideals. The overlap in the line chart is \(D(s)\).
-/

namespace ManuscriptAudit.CuspProperYChart

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CuspPunctured CuspProperCompactification CuspYChartAlgebra

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

variable (K : Type u) [Field K]

private abbrev L := LaurentPolynomial K
private abbrev yz := y K * z K
private abbrev YZChartRing := Away (grading K) (yz K)
private abbrev ZChartRing := Away (grading K) (z K)

private def cuspLaurent : CuspSubalgebra K →ₐ[K] L K :=
  Polynomial.toLaurentAlg.comp (CuspSubalgebra K).val

private def lineLaurent : Polynomial K →ₐ[K] L K :=
  LaurentPolynomial.invert.toAlgHom.comp Polynomial.toLaurentAlg

private def zValues (i : Fin 3) : L K :=
  if i = 0 then LaurentPolynomial.T 2 else if i = 1 then LaurentPolynomial.T 3 else 1

private def evalZLaurent : PlaneRing K →ₐ[K] L K :=
  MvPolynomial.aeval (zValues K)

private theorem evalZLaurent_y : evalZLaurent K (y K) = LaurentPolynomial.T 3 := by
  simp [evalZLaurent, zValues, y]

private theorem evalZLaurent_z : evalZLaurent K (z K) = 1 := by
  simp [evalZLaurent, zValues, z]

private theorem mul_T_three_neg_three :
    (LaurentPolynomial.T 3 : L K) * LaurentPolynomial.T (-3) = 1 := by
  rw [← LaurentPolynomial.T_add]
  norm_num

private theorem evalYZ_mul_inv :
    evalZLaurent K (yz K) * LaurentPolynomial.T (-3) = 1 := by
  rw [map_mul, evalZLaurent_y, evalZLaurent_z, mul_one]
  exact mul_T_three_neg_three K

private def evalYZ : YZChartRing K →+* L K :=
  fractionEvaluation K (evalZLaurent K).toRingHom (yz K) (LaurentPolynomial.T (-3))
    (evalYZ_mul_inv K)

private def yToYZ : YChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 2) (show yz K = y K * z K from rfl)

private def zToYZ : ZChartRing K →+* YZChartRing K :=
  awayMap (grading K) (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _)

private theorem affine_eval_laurent_mk (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K (n • 1)) :
    cuspLaurent K (affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
      evalZLaurent K p := by
  change Polynomial.toLaurentAlg
    ((affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp)) : Polynomial K) = _
  rw [affineChartEvaluation_mk_coe]
  change ((Polynomial.toLaurentAlg : Polynomial K →ₐ[K] L K).comp
    (MvPolynomial.aeval (fun i : Fin 3 => if i = 0 then Polynomial.X ^ 2
      else if i = 1 then Polynomial.X ^ 3 else 1))) p = MvPolynomial.aeval (zValues K) p
  rw [MvPolynomial.comp_aeval]
  apply congrArg (fun v : Fin 3 → L K => MvPolynomial.aeval v p)
  funext i
  fin_cases i <;> simp [zValues, Polynomial.toLaurent_X_pow]

private theorem scaled_values :
    (fun i => (LaurentPolynomial.T 3 : L K) * lineLaurent K (yValues K i)) = zValues K := by
  funext i
  fin_cases i <;>
    norm_num [lineLaurent, yValues, zValues, Polynomial.toLaurent_X_pow, ← LaurentPolynomial.T_add]

private theorem scaled_eval (n : ℕ) (p : PlaneRing K) (hp : p ∈ grading K n) :
    evalZLaurent K p = (LaurentPolynomial.T 3 : L K) ^ n * lineLaurent K (evalYPolynomial K p) := by
  unfold evalZLaurent
  rw [← scaled_values K, aeval_scale K _ _ hp]
  congr 1
  change _ = ((lineLaurent K).comp (MvPolynomial.aeval (yValues K))) p
  rw [MvPolynomial.comp_aeval]

private theorem evalYZ_on_z :
    (evalYZ K).comp (zToYZ K) = (cuspLaurent K).toRingHom.comp (affineChartEvaluation K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (X_mem_one K 2) b
  change evalYZ K (zToYZ K (Away.mk (grading K) (X_mem_one K 2) n p hp)) =
    cuspLaurent K (affineChartEvaluation K (Away.mk (grading K) (X_mem_one K 2) n p hp))
  unfold zToYZ
  rw [awayMap_mk, affine_eval_laurent_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZLaurent K (p * y K ^ n) * LaurentPolynomial.T (-3) ^ n = evalZLaurent K p
  rw [map_mul, map_pow, evalZLaurent_y, mul_assoc, ← mul_pow, mul_T_three_neg_three, one_pow, mul_one]

private theorem evalYZ_on_y :
    (evalYZ K).comp (yToYZ K) = (lineLaurent K).toRingHom.comp (evalYChart K) := by
  apply RingHom.ext
  intro b
  obtain ⟨n, p, hp, rfl⟩ := Away.mk_surjective (X_mem_one K 1) b
  change evalYZ K (yToYZ K (Away.mk (grading K) (X_mem_one K 1) n p hp)) =
    lineLaurent K (evalYChart K (Away.mk (grading K) (X_mem_one K 1) n p hp))
  unfold yToYZ
  rw [awayMap_mk, evalYChart_mk]
  unfold evalYZ
  rw [fractionEvaluation_mk]
  change evalZLaurent K (p * z K ^ n) * LaurentPolynomial.T (-3) ^ n =
    lineLaurent K (evalYPolynomial K p)
  rw [map_mul, map_pow, evalZLaurent_z, one_pow, mul_one]
  rw [scaled_eval K n p (by simpa only [nsmul_eq_mul, mul_one] using hp)]
  calc
    _ = lineLaurent K (evalYPolynomial K p) *
          ((LaurentPolynomial.T 3 : L K) ^ n * LaurentPolynomial.T (-3) ^ n) := by ac_rfl
    _ = _ := by rw [← mul_pow, mul_T_three_neg_three, one_pow, mul_one]

private def laurentToCusp : Spec (CommRingCat.of (L K)) ⟶ affineCusp K :=
  Spec.map (CommRingCat.ofHom (cuspLaurent K).toRingHom)

private def laurentToLine : Spec (CommRingCat.of (L K)) ⟶ Spec (CommRingCat.of (Polynomial K)) :=
  Spec.map (CommRingCat.ofHom (lineLaurent K).toRingHom)

private def yzChartι : Spec (CommRingCat.of (YZChartRing K)) ⟶ plane K :=
  Proj.awayι (grading K) (yz K) (SetLike.mul_mem_graded (X_mem_one K 1) (X_mem_one K 2))
    (by decide)

private theorem cuspPlaneViaYZ :
    laurentToCusp K ≫ cuspInPlane K =
      Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ yzChartι K := by
  have hmap :
      laurentToCusp K ≫ Spec.map (CommRingCat.ofHom (affineChartEvaluation K)) =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (zToYZ K)) := by
    unfold laurentToCusp
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_z K).symm)
  rw [cuspInPlane_as_Z_chart, ← Category.assoc, hmap, Category.assoc]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
    (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 2) (by decide)
      (X_mem_one K 1) (show yz K = z K * y K from mul_comm _ _))

private theorem linePlaneViaYZ :
    laurentToLine K ≫ lineInPlane K =
      Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ yzChartι K := by
  have hmap :
      laurentToLine K ≫ Spec.map (CommRingCat.ofHom (evalYChart K)) =
        Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ Spec.map (CommRingCat.ofHom (yToYZ K)) := by
    unfold laurentToLine
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (evalYZ_on_y K).symm)
  unfold lineInPlane
  rw [← Category.assoc, hmap, Category.assoc]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom (evalYZ K)) ≫ f)
    (Proj.SpecMap_awayMap_awayι (grading K) (X_mem_one K 1) (by decide)
      (X_mem_one K 2) (show yz K = y K * z K from rfl))

private theorem specMap_dominant_of_injective {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (hf : Function.Injective f) : IsDominant (Spec.map (CommRingCat.ofHom f)) := by
  constructor
  change DenseRange (PrimeSpectrum.comap f)
  apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical (f := f)).mpr
  rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
  exact bot_le

private theorem cuspKernel_lineKernel :
    (cuspInPlane K).ker = (lineInPlane K).ker := by
  haveI : IsDominant (laurentToCusp K) :=
    specMap_dominant_of_injective _ (Polynomial.toLaurent_injective.comp Subtype.val_injective)
  haveI : IsDominant (laurentToLine K) :=
    specMap_dominant_of_injective _
      (LaurentPolynomial.invert.injective.comp Polynomial.toLaurent_injective)
  haveI : IsSchemeTheoreticallyDominant (laurentToCusp K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  haveI : IsSchemeTheoreticallyDominant (laurentToLine K) :=
    IsSchemeTheoreticallyDominant.of_isDominant _
  have hC : (laurentToCusp K ≫ cuspInPlane K).ker = (cuspInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (laurentToCusp K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  have hY : (laurentToLine K ≫ lineInPlane K).ker = (lineInPlane K).ker := by
    rw [Scheme.Hom.ker_comp, (laurentToLine K).ker_eq_bot, Scheme.IdealSheafData.map_bot]
  exact hC.symm.trans ((congrArg Scheme.Hom.ker
    ((cuspPlaneViaYZ K).trans (linePlaneViaYZ K).symm)).trans hY)

private theorem imageIota_kernel_eq :
    (cuspInPlane K).imageι.ker = (lineInPlane K).imageι.ker := by
  change (cuspInPlane K).ker.subschemeι.ker = (lineInPlane K).ker.subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
    cuspKernel_lineKernel]

private def imageIso : (lineInPlane K).image ≅ projectiveCusp K :=
  letI := IsClosedImmersion.isIso_lift (cuspInPlane K).imageι (lineInPlane K).imageι
    (imageIota_kernel_eq K)
  asIso (IsClosedImmersion.lift (cuspInPlane K).imageι (lineInPlane K).imageι
    (imageIota_kernel_eq K).le)

/-- The line as an actual open chart of the proper cusp. -/
def lineOpen : Spec (CommRingCat.of (Polynomial K)) ⟶ projectiveCusp K :=
  (lineInPlane K).toImage ≫ (imageIso K).hom

instance lineOpen_isOpenImmersion : IsOpenImmersion (lineOpen K) := by
  letI := lineInPlane_isImmersion K
  letI : QuasiCompact (lineInPlane K) := quasiCompact_of_compactSpace _
  unfold lineOpen
  infer_instance

theorem lineOpen_inPlane : lineOpen K ≫ (cuspInPlane K).imageι = lineInPlane K := by
  unfold lineOpen imageIso
  simp only [Category.assoc, asIso_hom, IsClosedImmersion.lift_fac, Scheme.Hom.toImage_imageι]

def yOpen : (projectiveCusp K).Opens :=
  (cuspInPlane K).imageι ⁻¹ᵁ Proj.basicOpen (grading K) (y K)

theorem lineOpen_range : (lineOpen K).opensRange = yOpen K := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    change ((lineOpen K) ≫ (cuspInPlane K).imageι) t ∈ Proj.basicOpen (grading K) (y K)
    rw [lineOpen_inPlane,
      ← Proj.opensRange_awayι (grading K) (y K) (X_mem_one K 1) (by decide)]
    exact ⟨Spec.map (CommRingCat.ofHom (evalYChart K)) t, rfl⟩
  · intro hx
    let g := Spec.map (CommRingCat.ofHom (evalYChart K))
    haveI : IsClosedImmersion g :=
      IsClosedImmersion.spec_of_surjective _ (evalYChart_surjective K)
    have hi : (cuspInPlane K).imageι x ∈ Set.range (yChartι K) := by
      change (cuspInPlane K).imageι x ∈ (yChartι K).opensRange
      rw [Proj.opensRange_awayι]
      exact hx
    obtain ⟨q, hq⟩ := hi
    have hClose : closure (Set.range (lineInPlane K)) = Set.range (cuspInPlane K).imageι := by
      letI : QuasiCompact (lineInPlane K) := quasiCompact_of_compactSpace _
      rw [← Scheme.Hom.support_ker, ← cuspKernel_lineKernel]
      exact (Scheme.IdealSheafData.range_subschemeι _).symm
    have hqClosure : yChartι K q ∈ closure (Set.range (lineInPlane K)) := by
      rw [hq, hClose]
      exact ⟨x, rfl⟩
    have hRange : Set.range (lineInPlane K) = (yChartι K) '' Set.range g := by
      change Set.range ((yChartι K) ∘ g) = _
      exact Set.range_comp _ _
    have he := (yChartι K).isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image
      (Set.range g)
    rw [g.isClosedEmbedding.isClosed_range.closure_eq, ← hRange] at he
    have hqImage : q ∈ Set.range g := by rw [he]; exact hqClosure
    obtain ⟨t, ht⟩ := hqImage
    refine ⟨t, (cuspInPlane K).imageι.isClosedEmbedding.injective ?_⟩
    calc
      _ = lineInPlane K t := by
        change ((lineOpen K) ≫ (cuspInPlane K).imageι) t = _
        rw [lineOpen_inPlane]
      _ = yChartι K q := by change yChartι K (g t) = _; rw [ht]
      _ = _ := hq

/-- The native open \(Y\ne0\) of the proper cusp is isomorphic to the affine line. -/
def yOpenIsoAffineLine : (yOpen K).toScheme ≅ Spec (CommRingCat.of (Polynomial K)) := by
  letI := lineOpen_isOpenImmersion K
  apply IsOpenImmersion.isoOfRangeEq (yOpen K).ι (lineOpen K)
  rw [Scheme.Opens.range_ι]
  change (yOpen K : Set (projectiveCusp K)) = ((lineOpen K).opensRange : Set (projectiveCusp K))
  rw [lineOpen_range]

theorem lineOpen_preimage_affine :
    (lineOpen K) ⁻¹ᵁ (affineOpen K).opensRange =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K) := by
  rw [affineOpen_opensRange_eq, ← Scheme.Hom.comp_preimage, lineOpen_inPlane, lineInPlane_preimage_z]

theorem affine_chart_cover :
    (affineOpen K).opensRange ⊔ (lineOpen K).opensRange = ⊤ := by
  apply top_unique
  intro p _
  change p ∈ (affineOpen K).opensRange ∨ p ∈ (lineOpen K).opensRange
  by_cases hp : p ∈ (affineOpen K).opensRange
  · exact Or.inl hp
  · right
    rw [lineOpen_range]
    exact (Proj.mem_basicOpen _ _ _).mpr (boundary_plane_coordinates K p hp).2.2

theorem affine_chart_overlap_isConnected :
    IsConnected ((((affineOpen K).opensRange ⊓ (lineOpen K).opensRange :
      (projectiveCusp K).Opens)) : Set (projectiveCusp K)) := by
  have hImage :
      (lineOpen K) '' ((lineOpen K) ⁻¹ᵁ (affineOpen K).opensRange :
        Set (Spec (CommRingCat.of (Polynomial K)))) =
        (((affineOpen K).opensRange ⊓ (lineOpen K).opensRange :
          (projectiveCusp K).Opens) : Set (projectiveCusp K)) := by
    exact Set.image_preimage_eq_inter_range
  rw [← hImage, lineOpen_preimage_affine]
  exact ((punctured_line_irreducible K).image _ (lineOpen K).continuous.continuousOn).isConnected

end

end ManuscriptAudit.CuspProperYChart

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CuspProperYChart.lineOpen_isOpenImmersion,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_inPlane,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_range,
      ``ManuscriptAudit.CuspProperYChart.yOpenIsoAffineLine,
      ``ManuscriptAudit.CuspProperYChart.lineOpen_preimage_affine,
      ``ManuscriptAudit.CuspProperYChart.affine_chart_cover,
      ``ManuscriptAudit.CuspProperYChart.affine_chart_overlap_isConnected] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
