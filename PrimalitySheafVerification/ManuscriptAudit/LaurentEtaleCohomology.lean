import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
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
  rw [H.map_zero]
  exact h

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

end

end ManuscriptAudit.LaurentEtaleCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.LaurentEtaleCohomology.laurent_HOne_roots_nonzero,
      ``ManuscriptAudit.LaurentEtaleCohomology.laurent_HOne_cyclic_nonzero,
      ``ManuscriptAudit.LaurentEtaleCohomology.cusp_punctured_HOne_cyclic_nonzero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
