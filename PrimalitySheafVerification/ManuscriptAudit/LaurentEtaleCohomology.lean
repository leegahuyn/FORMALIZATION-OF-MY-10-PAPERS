import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspPicard
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology
import PrimalitySheafVerification.ManuscriptAudit.LaurentUnits

/-!
# A nonzero Kummer class on the Laurent affine scheme

The boundary class of the Laurent coordinate is nonzero for degree at
least two. This proves nonvanishing of cohomology with constant cyclic
coefficients on the small affine étale site of the punctured cusp.
-/

namespace ManuscriptAudit.LaurentEtaleCohomology

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian LaurentPolynomial
open KummerAffineCohomology KummerConstantCoefficients

noncomputable section

variable (K : Type) [Field K] [IsAlgClosed K]

private abbrev laurentRing : CommRingCat.{0} := CommRingCat.of (LaurentPolynomial K)
private abbrev cuspRing : CommRingCat.{0} :=
  CommRingCat.of (Localization.Away (CuspPunctured.cuspSquare K))
private abbrev affineSite (R : CommRingCat.{0}) := Scheme.AffineEtale.topology (Spec R)

attribute [local instance] KummerCohomologySequence.affineSiteHasExt

private theorem rootsNonzeroOfLaurentCoordinates (R : CommRingCat.{0}) [Algebra K R]
    (e : R ≃ₐ[K] LaurentPolynomial K) (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ c : Sheaf.H ((constantSheaf (affineSite R) AddCommGrpCat.{0}).obj
      (coefficientGroup K d)) 1, c ≠ 0 := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  let t₀ : (LaurentPolynomial K)ˣ := unitOfInvertible (T 1 : LaurentPolynomial K)
  let t : Rˣ := Units.map e.symm.toRingHom.toMonoidHom t₀
  have hpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hdeg
  have hd : IsUnit (d : R) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K R)
  refine ⟨unitBoundary (K := K) R d hpos hd (Additive.ofMul t), ?_⟩
  intro h
  obtain ⟨v, hv⟩ := (unitBoundary_eq_zero_iff (K := K) R d hpos hd (Additive.ofMul t)).mp h
  let eᵤ := Units.map e.toRingHom.toMonoidHom
  have he : eᵤ t = t₀ := Units.ext (e.apply_symm_apply (t₀ : LaurentPolynomial K))
  have hv' := congrArg eᵤ hv
  change eᵤ (v ^ d) = eᵤ t at hv'
  rw [map_pow, he] at hv'
  apply LaurentUnits.laurent_T_one_not_unit_pow K hdeg (eᵤ v)
  exact congrArg (fun u : (LaurentPolynomial K)ˣ => (u : LaurentPolynomial K)) hv'

private theorem cyclicNonzeroOfLaurentCoordinates (R : CommRingCat.{0}) [Algebra K R]
    (e : R ≃ₐ[K] LaurentPolynomial K) (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ c : Sheaf.H ((constantSheaf (affineSite R) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1, c ≠ 0 := by
  let r : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let g := (constantSheaf (affineSite R) AddCommGrpCat.{0}).mapIso
    (r.toAddCommGrpIso : coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let H := ((Sheaf.functorH (affineSite R) 1).mapIso g).addCommGroupIsoToAddEquiv
  obtain ⟨c, hc⟩ := rootsNonzeroOfLaurentCoordinates K R e d hdeg
  refine ⟨H c, ?_⟩
  intro h
  apply hc
  apply H.injective
  exact h.trans H.map_zero.symm

/-- The class of the Laurent generator gives a nonzero degree-one class
in the actual constant roots-of-unity sheaf. -/
theorem laurent_HOne_roots_nonzero (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ c : Sheaf.H ((constantSheaf (affineSite (laurentRing K)) AddCommGrpCat.{0}).obj
      (coefficientGroup K d)) 1, c ≠ 0 :=
  rootsNonzeroOfLaurentCoordinates K (laurentRing K) (AlgEquiv.refl) d hdeg

/-- The Laurent affine scheme has nonzero degree-one cohomology with
constant cyclic coefficients on its small affine étale site. -/
theorem laurent_HOne_cyclic_nonzero (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ c : Sheaf.H ((constantSheaf (affineSite (laurentRing K)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1, c ≠ 0 :=
  cyclicNonzeroOfLaurentCoordinates K (laurentRing K) (AlgEquiv.refl) d hdeg

/-- The actual punctured cusp coordinate ring has nonzero degree-one
cohomology with constant cyclic coefficients on its small affine étale site. -/
theorem cusp_punctured_HOne_cyclic_nonzero (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ c : Sheaf.H ((constantSheaf (affineSite (cuspRing K)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1, c ≠ 0 :=
  cyclicNonzeroOfLaurentCoordinates K (cuspRing K)
    (CuspPunctured.paper2_cusp_punctured_coordinate_equiv K) d hdeg

/-- On the ordinary affine line the actual Kummer boundary of every
unit is zero, since every polynomial unit has a power root. -/
theorem affineLine_unitBoundary_zero (d : ℕ) [NeZero d] [NeZero (d : K)]
    (hpos : 0 < d) (hd : IsUnit (d : Polynomial K)) :
    unitBoundary (K := K) (CommRingCat.of (Polynomial K)) d hpos hd = 0 := by
  apply AddMonoidHom.ext
  intro y
  change unitBoundary (K := K) (CommRingCat.of (Polynomial K)) d hpos hd y = 0
  apply (unitBoundary_eq_zero_iff (K := K) (CommRingCat.of (Polynomial K)) d hpos hd y).mpr
  exact CuspPicard.paper2_polynomial_unit_power_surjective K d hpos y.toMul

private def exponentUnit (R : CommRingCat.{0}) [Algebra K R]
    (e : R ≃ₐ[K] LaurentPolynomial K) : ℤ →+ Additive Rˣ where
  toFun n := Additive.ofMul
    (Units.map e.symm.toRingHom.toMonoidHom (unitOfInvertible (T n : LaurentPolynomial K)))
  map_zero' := by
    apply Additive.ext
    apply Units.ext
    change e.symm (T 0) = 1
    simp
  map_add' m n := by
    apply Additive.ext
    apply Units.ext
    change e.symm (T (m + n)) = e.symm (T m) * e.symm (T n)
    rw [T_add, map_mul]

private theorem rootsCyclicEmbedsOfLaurentCoordinates (R : CommRingCat.{0}) [Algebra K R]
    (e : R ≃ₐ[K] LaurentPolynomial K) (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ i : ZMod d →+ Sheaf.H ((constantSheaf (affineSite R) AddCommGrpCat.{0}).obj
      (coefficientGroup K d)) 1, Function.Injective i ∧
      (Subsingleton (Sheaf.H (KummerSheafSequence.unitSheaf (Spec R)) 1) →
        Function.Surjective i) := by
  letI : NeZero d := NeZero.of_neZero_natCast K
  have hpos : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) hdeg
  have hd : IsUnit (d : R) := by
    have hk : IsUnit (d : K) := isUnit_iff_ne_zero.mpr (NeZero.ne _)
    simpa only [map_natCast] using hk.map (algebraMap K R)
  let q := exponentUnit K R e
  let b := unitBoundary (K := K) R d hpos hd
  let h := b.comp q
  have hKer (n : ℤ) : h n = 0 ↔ (d : ℤ) ∣ n := by
    change unitBoundary (K := K) R d hpos hd (q n) = 0 ↔ _
    rw [unitBoundary_eq_zero_iff]
    constructor
    · rintro ⟨v, hv⟩
      have hVal := congrArg (fun z : Rˣ => e (z : R)) hv
      change e ((v ^ d : Rˣ) : R) = e (e.symm (T n)) at hVal
      rw [Units.val_pow_eq_pow_val, map_pow, AlgEquiv.apply_symm_apply] at hVal
      refine (LaurentUnits.laurent_monomial_unit_pow_iff K hpos (one_ne_zero : (1 : K) ≠ 0) n).mp
        ⟨Units.map e.toRingHom.toMonoidHom v, ?_⟩
      change e (v : R) ^ d = LaurentPolynomial.C (1 : K) * T n
      simpa only [map_one, one_mul] using hVal
    · intro hn
      obtain ⟨v, hv⟩ := (LaurentUnits.laurent_monomial_unit_pow_iff K hpos
        (one_ne_zero : (1 : K) ≠ 0) n).mpr hn
      refine ⟨Units.map e.symm.toRingHom.toMonoidHom v, Units.ext ?_⟩
      rw [Units.val_pow_eq_pow_val]
      change (e.symm (v : LaurentPolynomial K)) ^ d = e.symm (T n)
      rw [← map_pow, hv, map_one, one_mul]
  have hdZero : h (d : ℤ) = 0 := (hKer (d : ℤ)).mpr dvd_rfl
  refine ⟨ZMod.lift d ⟨h, hdZero⟩, ?_, ?_⟩
  · rw [ZMod.lift_injective]
    intro n hn
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n d).mpr ((hKer n).mp hn)
  · intro hUnit x
    obtain ⟨u, hu⟩ := unitBoundary_surjective_of_unitHOne (K := K) R d hpos hd hUnit x
    let uL : (LaurentPolynomial K)ˣ := Units.map e.toRingHom.toMonoidHom u.toMul
    obtain ⟨r, _, _, v, hv⟩ := LaurentUnits.laurent_unit_has_power_residue K hpos uL
    let vR : Rˣ := Units.map e.symm.toRingHom.toMonoidHom v
    have hMul : vR ^ d * (q r).toMul = u.toMul := by
      apply Units.ext
      rw [Units.val_mul, Units.val_pow_eq_pow_val]
      change (e.symm (v : LaurentPolynomial K)) ^ d * e.symm (T r) = (u.toMul : R)
      have hVal := congrArg (fun z : LaurentPolynomial K => e.symm z) hv.symm
      change e.symm ((v : LaurentPolynomial K) ^ d * T r) =
        e.symm (e (u.toMul : R)) at hVal
      simpa only [map_mul, map_pow, AlgEquiv.symm_apply_apply] using hVal
    have hAdd : Additive.ofMul (vR ^ d) + q r = u := Additive.ext hMul
    have hz : b (Additive.ofMul (vR ^ d)) = 0 :=
      (unitBoundary_eq_zero_iff (K := K) R d hpos hd (Additive.ofMul (vR ^ d))).mpr ⟨vR, rfl⟩
    refine ⟨(r : ZMod d), ?_⟩
    rw [ZMod.lift_coe]
    change b (q r) = x
    calc
      _ = b (Additive.ofMul (vR ^ d)) + b (q r) := by rw [hz, zero_add]
      _ = b (Additive.ofMul (vR ^ d) + q r) := (map_add b _ _).symm
      _ = x := by rw [hAdd]; exact hu

/-- The punctured cusp has a subgroup of actual H¹ isomorphic to the full
cyclic coefficient group. Its classes come from Laurent coordinate units. -/
theorem cusp_punctured_cyclic_HOne_contains (d : ℕ) [NeZero (d : K)] (hdeg : 2 ≤ d) :
    ∃ i : ZMod d →+ Sheaf.H ((constantSheaf (affineSite (cuspRing K)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1, Function.Injective i := by
  let R := cuspRing K
  let r : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let g := (constantSheaf (affineSite R) AddCommGrpCat.{0}).mapIso
    (r.toAddCommGrpIso : coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let H := ((Sheaf.functorH (affineSite R) 1).mapIso g).addCommGroupIsoToAddEquiv
  obtain ⟨i, hi, _⟩ := rootsCyclicEmbedsOfLaurentCoordinates K R
    (CuspPunctured.paper2_cusp_punctured_coordinate_equiv K) d hdeg
  exact ⟨H.toAddMonoidHom.comp i, H.injective.comp hi⟩

/-- With the unit sheaf's actual first cohomology zero, the entire
punctured cusp coefficient group is the cyclic group of Laurent exponents. -/
theorem cusp_punctured_cyclic_HOne_equiv_of_unitHOne (d : ℕ) [NeZero (d : K)]
    (hdeg : 2 ≤ d)
    (hUnit : Subsingleton (Sheaf.H (KummerSheafSequence.unitSheaf (Spec (cuspRing K))) 1)) :
    Nonempty (ZMod d ≃+ Sheaf.H ((constantSheaf (affineSite (cuspRing K)) AddCommGrpCat.{0}).obj
      (AddCommGrpCat.of (ZMod d))) 1) := by
  let R := cuspRing K
  let r : Additive (rootsOfUnity d K) ≃+ ZMod d :=
    (CuspRootCoefficients.rootsOfUnityEquivZMod K d).toAdditive
  let g := (constantSheaf (affineSite R) AddCommGrpCat.{0}).mapIso
    (r.toAddCommGrpIso : coefficientGroup K d ≅ AddCommGrpCat.of (ZMod d))
  let H := ((Sheaf.functorH (affineSite R) 1).mapIso g).addCommGroupIsoToAddEquiv
  obtain ⟨i, hi, hs⟩ := rootsCyclicEmbedsOfLaurentCoordinates K R
    (CuspPunctured.paper2_cusp_punctured_coordinate_equiv K) d hdeg
  exact ⟨(AddEquiv.ofBijective i ⟨hi, hs hUnit⟩).trans H⟩

/-- The polynomial unit roots and the Kummer boundary identify ordinary
affine-line H¹ when the unit sheaf has trivial H¹. -/
theorem affineLine_HOne_roots_subsingleton_of_unitHOne
    (d : ℕ) [NeZero d] [NeZero (d : K)] (hpos : 0 < d) (hd : IsUnit (d : Polynomial K))
    (hUnit : Subsingleton (Sheaf.H (KummerSheafSequence.unitSheaf
      (Spec (CommRingCat.of (Polynomial K)))) 1)) :
    Subsingleton (Sheaf.H ((constantSheaf (affineSite (CommRingCat.of (Polynomial K)))
      AddCommGrpCat.{0}).obj (coefficientGroup K d)) 1) := by
  refine subsingleton_of_forall_eq 0 (fun x => ?_)
  obtain ⟨u, rfl⟩ := unitBoundary_surjective_of_unitHOne (K := K)
    (CommRingCat.of (Polynomial K)) d hpos hd hUnit x
  exact DFunLike.congr_fun (affineLine_unitBoundary_zero K d hpos hd) u

end

end ManuscriptAudit.LaurentEtaleCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentEtaleCohomology.laurent_HOne_roots_nonzero,
      ``ManuscriptAudit.LaurentEtaleCohomology.laurent_HOne_cyclic_nonzero,
      ``ManuscriptAudit.LaurentEtaleCohomology.cusp_punctured_HOne_cyclic_nonzero,
      ``ManuscriptAudit.LaurentEtaleCohomology.affineLine_unitBoundary_zero,
      ``ManuscriptAudit.LaurentEtaleCohomology.cusp_punctured_cyclic_HOne_contains,
      ``ManuscriptAudit.LaurentEtaleCohomology.cusp_punctured_cyclic_HOne_equiv_of_unitHOne,
      ``ManuscriptAudit.LaurentEtaleCohomology.affineLine_HOne_roots_subsingleton_of_unitHOne] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
