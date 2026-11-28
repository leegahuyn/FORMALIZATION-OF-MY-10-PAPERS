import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspLaurentNativeCoverGeometry
import PrimalitySheafVerification.ManuscriptAudit.ProetaleFreeAffineUnits
import PrimalitySheafVerification.ManuscriptAudit.ProetaleUnitRestriction
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnitProductCoordinates

/-! The native first free term of the cusp cover has scalar relative
power action on Kummer cohomology. -/

namespace ManuscriptAudit.CuspNativeLaurentFreeKummerPower

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp projectiveCuspToBase affineOpen)
open CuspProperYChart (lineOpen)
open CuspNativeProetaleHTwoLower (cover)
open CuspLaurentNativeCoverGeometry (inclusion first second native_isPullback relative_cartesian)
open CuspRelativePowerCoordinates (laurentPower laurentPower_T)
open CuspRelativePowerMap (overlapMap projectiveMap)
open ProetaleOpenLocalLifts (openObject)
open ProetaleMayerVietorisRepresentable (nativeFree)
open ProetaleMayerVietorisConnecting (firstEquiv)
open ProetaleUnitSheaf (unitSheaf)
open ProetaleUnitRestriction (restrictionUnitsIso)
open ProetaleKummerPower (power)
open ProetaleKummerSequence (sequence sequence_shortExact)
open ProetaleKummerSchemePullback (unitsPullback kernelPullback sequencePullback)
open ProetaleFreeAffineUnits (coordinates coordinates_pullback)
open ProetaleCohomologyIso (cohomologyIso)
open LaurentUnitProductCoordinates (unitCoordinates unitCoordinates_apply)
open KummerUnitsSheaf (ringUnits)
open scoped nonZeroDivisors

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev X := projectiveCusp K
private abbrev L := LaurentPolynomial K
private abbrev W := openObject (inclusion K)
private abbrev I := nativeFree (W K)
private abbrev F := unitSheaf (X K)

private theorem open_hom :
    (W K).hom = inclusion K := by
  change 𝟙 _ ≫ inclusion K = inclusion K
  exact Category.id_comp _

variable (m : ℕ) (hm : 2 ≤ m)

private abbrev f := projectiveMap K m hm
private abbrev a := CommRingCat.ofHom (laurentPower K m).toRingHom

theorem overlapCart :
    IsPullback (Spec.map (a K m)) (W K).hom (W K).hom (f K m hm) := by
  simpa only [open_hom] using relative_cartesian K m hm

abbrev e := ProetaleCartesianChartIso.chartIso (f K m hm) (overlapCart K m hm)

private def coordinates' : Ext (I K) (F K) 0 ≃+ Additive Kˣ × ℤ :=
  (coordinates (inclusion K)).trans (unitCoordinates K).symm

private theorem unitPower (x : Additive Kˣ) (i : ℤ) :
    (ringUnits.map (a K m)) (unitCoordinates K (x, i)) =
      unitCoordinates K (x, i * (m : ℤ)) := by
  apply Additive.ext
  apply Units.ext
  change laurentPower K m ((unitCoordinates K (x, i)).toMul : L K) =
    ((unitCoordinates K (x, i * (m : ℤ))).toMul : L K)
  rw [unitCoordinates_apply, unitCoordinates_apply, map_mul, laurentPower_T]
  have h : laurentPower K m (LaurentPolynomial.C (x.toMul : K)) =
      LaurentPolynomial.C (x.toMul : K) := (laurentPower K m).commutes _
  rw [h]

private theorem coordinate_power (u : Ext (I K) (F K) 0) :
    coordinates' K (ProetaleFreeExtPullback.map (f K m hm) (e K m hm)
      (unitsPullback (f K m hm)) 0 u) = ((coordinates' K u).1, (coordinates' K u).2 * (m : ℤ)) := by
  let c := coordinates' K
  obtain ⟨⟨x, i⟩, rfl⟩ := c.symm.surjective u
  have h := coordinates_pullback (inclusion K) (inclusion K) (f K m hm) (a K m)
    (overlapCart K m hm) (c.symm (x, i))
  have hcoord : coordinates (inclusion K) (c.symm (x, i)) = unitCoordinates K (x, i) :=
    (coordinates (inclusion K)).apply_symm_apply _
  rw [hcoord, unitPower K m] at h
  change (unitCoordinates K).symm (coordinates (inclusion K)
    (ProetaleFreeExtPullback.map (f K m hm) (e K m hm) (unitsPullback (f K m hm)) 0 (c.symm (x, i)))) =
    ((c (c.symm (x, i))).1, (c (c.symm (x, i))).2 * (m : ℤ))
  rw [h, AddEquiv.symm_apply_apply, AddEquiv.apply_symm_apply]

variable (d : ℕ) [NeZero (d : K)]

local instance residueOrder : NeZero d := NeZero.of_neZero_natCast K

private theorem scalar_root (x : Additive Kˣ) : ∃ y : Additive Kˣ, d • y = x := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (x.toMul : K) (Nat.pos_of_ne_zero (NeZero.ne d))
  have hn : y ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne d)] at hy
    exact x.toMul.ne_zero hy.symm
  refine ⟨Additive.ofMul (Units.mk0 y hn), Additive.ext (Units.ext ?_)⟩
  exact hy

private theorem power_mod_scalar (u : Ext (I K) (F K) 0) :
    ∃ v : Ext (I K) (F K) 0, ProetaleFreeExtPullback.map (f K m hm) (e K m hm)
      (unitsPullback (f K m hm)) 0 u = m • u + d • v := by
  let c := coordinates' K
  let x := (c u).1
  obtain ⟨y, hy⟩ := scalar_root K d (x - m • x)
  let v := c.symm (y, 0)
  refine ⟨v, c.injective ?_⟩
  change coordinates' K (ProetaleFreeExtPullback.map (f K m hm) (e K m hm)
    (unitsPullback (f K m hm)) 0 u) = c (m • u + d • v)
  rw [coordinate_power, map_add, map_nsmul, map_nsmul]
  have hv : c v = (y, 0) := c.apply_symm_apply _
  rw [hv]
  apply Prod.ext
  · change x = m • x + d • y
    rw [hy, add_comm (m • x), sub_add_cancel]
  · change (c u).2 * (m : ℤ) = m • (c u).2 + d • (0 : ℤ)
    rw [nsmul_zero, add_zero, nsmul_eq_mul, mul_comm]

local instance laurentDomain : IsDomain (L K) :=
  IsLocalization.isDomain_of_le_nonZeroDivisors (L K)
    (show Submonoid.powers (Polynomial.X : Polynomial K) ≤ (Polynomial K)⁰ from by
      rintro _ ⟨n, rfl⟩
      exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero n Polynomial.X_ne_zero))

local instance laurentPID : IsPrincipalIdealRing (L K) := ⟨fun J ↦ by
  rw [← IsLocalization.map_under (Submonoid.powers (Polynomial.X : Polynomial K)) (L K) J]
  exact Submodule.IsPrincipal.map_ringHom (algebraMap (Polynomial K) (L K))
    (inferInstance : (J.under (Polynomial K)).IsPrincipal)⟩

private abbrev hS := sequence_shortExact (projectiveCuspToBase K) d
private abbrev δ : Ext (I K) (F K) 0 →+ Ext (I K) (kernel (power (X K) d)) 1 :=
  (hS K d).extClass.postcomp (I K) rfl

private theorem boundary_surjective : Function.Surjective (δ K d) := by
  let i := firstEquiv (affineOpen K) (lineOpen K) (inclusion K) (first K) (second K)
    (native_isPullback K) (cover K) (F K) 1
  let j := i.trans (cohomologyIso (restrictionUnitsIso (inclusion K)) 1)
  have h := ProetalePIDUnitHOne.HOne_subsingleton (L K)
  have hn : Subsingleton (Ext (I K) (F K) 1) :=
    ⟨fun a b ↦ j.injective (h.elim _ _)⟩
  intro z
  exact Ext.covariant_sequence_exact₁ (I K) (hS K d) z (hn.elim _ _) (n₀ := 0) rfl

private theorem boundary_power_zero (u : Ext (I K) (F K) 0) : δ K d (d • u) = 0 := by
  have hExact := Ext.covariant_sequence_exact₃' (I K) (hS K d) 0 1 rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at hExact
  apply (hExact (d • u)).2
  refine ⟨u, ?_⟩
  obtain ⟨b, rfl⟩ := (Ext.mk₀_bijective (I K) (F K)).surjective u
  let j : (I K ⟶ F K) ≃+ Ext (I K) (F K) 0 := Ext.addEquiv₀.symm
  change (Ext.mk₀ b).comp (Ext.mk₀ (power (X K) d)) rfl = d • Ext.mk₀ b
  rw [Ext.mk₀_comp_mk₀]
  change j (b ≫ power (X K) d) = d • j b
  rw [power, Preadditive.comp_nsmul, Category.comp_id, map_nsmul]

set_option maxHeartbeats 8200000 in
/-- The exact proper cusp cover's first free term has scalar pullback in native Kummer H¹. -/
theorem kernel_scalar (z : Ext (I K) (kernel (power (X K) d)) 1) :
    ProetaleFreeExtPullback.map (f K m hm) (e K m hm)
      (kernelPullback (f K m hm) d) 1 z = m • z := by
  obtain ⟨u, rfl⟩ := boundary_surjective K d z
  have h := ProetaleFreeExtPullback.map_boundary (f K m hm) (e K m hm)
    (hS K d) (hS K d) (sequencePullback (f K m hm) d) 0 u
  change _ = δ K d (ProetaleFreeExtPullback.map (f K m hm) (e K m hm)
    (unitsPullback (f K m hm)) 0 u) at h
  rw [h]
  obtain ⟨v, hv⟩ := power_mod_scalar K m hm d u
  rw [hv, map_add, map_nsmul, boundary_power_zero, add_zero]

end
end ManuscriptAudit.CuspNativeLaurentFreeKummerPower

open Lean Elab Command in
run_cmd do
  let n := ``ManuscriptAudit.CuspNativeLaurentFreeKummerPower.kernel_scalar
  let ax ← collectAxioms n
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  unless ax.all (fun a ↦ allowed.contains a) do
    throwError m!"{n} depends on unexpected axioms {ax}"
  logInfo m!"{n} uses {ax}"
