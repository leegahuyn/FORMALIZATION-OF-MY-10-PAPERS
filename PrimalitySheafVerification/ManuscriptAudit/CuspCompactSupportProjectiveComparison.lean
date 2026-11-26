import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import PrimalitySheafVerification.ManuscriptAudit.CuspCompactSupportSequence
import PrimalitySheafVerification.ManuscriptAudit.CuspInfinitySupport
import PrimalitySheafVerification.ManuscriptAudit.GeometricSkyscraperHigherCohomology
import PrimalitySheafVerification.ManuscriptAudit.RationalPointQuotientHZero

/-!
# Positive compact-support cohomology of the affine cusp in its proper closure

The genuine compactification omits the single rational infinity point.
The actual quotient map is onto in degree zero, and its closed term
has no higher cohomology. Consequently the canonical open-extension
map is an isomorphism on cohomology in every positive degree.
-/

namespace ManuscriptAudit.CuspCompactSupportSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open CuspProperCompactification CuspRationalInfinity CuspInfinitySupport
open OpenEtaleExtension SmallEtaleGeometricBaseChange GeometricSkyscraperCohomology

universe u

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local instance] etaleSiteHasExt

private abbrev C := AddCommGrpCat.{u}

private theorem positiveMap_bijective {X : Scheme.{u}}
    (S : ShortComplex (Sheaf X.smallEtaleTopology C.{u})) (hS : S.ShortExact)
    (h₀ : Function.Surjective (Sheaf.H.map S.g 0))
    (h₊ : ∀ n : ℕ, Subsingleton (Sheaf.H S.X₃ (n + 1))) (n : ℕ) :
    Function.Bijective (Sheaf.H.map S.f (n + 1)) := by
  let Z := (constantSheaf X.smallEtaleTopology C.{u}).obj
    (AddCommGrpCat.of (ULift.{u} ℤ))
  have hδ (a : ℕ) (x : Sheaf.H S.X₃ a) :
      x.comp hS.extClass (show a + 1 = a + 1 from rfl) = 0 := by
    cases a with
    | zero =>
      have hExact : Function.Exact (Sheaf.H.map S.g 0)
          (hS.extClass.postcomp Z (show 0 + 1 = 1 from rfl)) :=
        (ShortComplex.ab_exact_iff_function_exact _).mp (Ext.covariant_sequence_exact₃' Z hS 0 1 rfl)
      exact (hExact x).mpr (h₀ x)
    | succ a =>
      have hx : x = 0 := (h₊ a).allEq _ _
      rw [hx, Ext.zero_comp]
  constructor
  · intro x y hxy
    have hz : (Sheaf.H.map S.f (n + 1)) (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    obtain ⟨t, ht⟩ := Ext.covariant_sequence_exact₁ (X := Z) hS (x - y) hz
      (show n + 1 = n + 1 from rfl)
    exact sub_eq_zero.mp (ht.symm.trans (hδ n t))
  · intro y
    have hy : y.comp (Ext.mk₀ S.g) (add_zero (n + 1)) = 0 := (h₊ n).allEq _ _
    exact Ext.covariant_sequence_exact₂ (X := Z) hS y hy

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev P := projectiveCusp K
private abbrev o := infinityPoint K ≫ 𝟙 (P K)

private theorem infinity_closed : IsClosedImmersion (o K) := by
  simpa only [o, Category.comp_id] using infinityPoint_isClosedImmersion K

private theorem affine_range : Set.range (affineOpen K) = (Set.range (infinityPoint K))ᶜ := by
  simpa using congrArg (fun U : Set (P K) => Uᶜ) (affine_complement_eq_infinity K)

private def infinitySequence (M : C.{u}) :
    ShortComplex (Sheaf (P K).smallEtaleTopology C.{u}) :=
  letI := affineOpen_isOpenImmersion K
  letI := infinity_closed K
  nestedOpenRationalOriginSequence (affineOpen K) (𝟙 (P K)) M (infinityPoint K) (affine_range K)

private theorem infinitySequence_shortExact (M : C.{u}) : (infinitySequence K M).ShortExact := by
  letI := affineOpen_isOpenImmersion K
  letI := infinity_closed K
  exact nestedOpenRationalOriginSequence_shortExact (affineOpen K) (𝟙 (P K)) M
    (infinityPoint K) (affine_range K)

private theorem infinitySequence_HZero_surjective (M : C.{u}) :
    Function.Surjective (Sheaf.H.map (infinitySequence K M).g 0) := by
  letI := affineOpen_isOpenImmersion K
  letI := infinity_closed K
  exact rationalPointQuotient_HZero_surjective (affineOpen K) M (infinityPoint K) (affine_range K)

private theorem infinitySequence_boundary_H_succ (M : C.{u}) (n : ℕ) :
    Subsingleton (Sheaf.H (infinitySequence K M).X₃ (n + 1)) := by
  let Φ := Scheme.pointSmallEtale (o K)
  let e₀ : (infinitySequence K M).X₃ ≅ Φ.skyscraperSheaf M :=
    rationalPointConstantDirectImageIso K (o K) M
  let e : Sheaf.H (infinitySequence K M).X₃ (n + 1) ≃+
      Sheaf.H (Φ.skyscraperSheaf M) (n + 1) :=
    ((Sheaf.functorH (P K).smallEtaleTopology (n + 1)).mapIso e₀).addCommGroupIsoToAddEquiv
  have h := geometricSkyscraperH_succ_subsingleton Φ M n
  exact ⟨fun x y => e.injective (h.allEq (e x) (e y))⟩

private def infinitySequence_firstIso (M : C.{u}) :
    (infinitySequence K M).X₁ ≅ (compactSupportSequence K M).X₂ := by
  letI := affineOpen_isOpenImmersion K
  let J := extensionByZero (affineOpen K) C.{u}
  let G := (constantSheaf (affineCusp K).smallEtaleTopology C.{u}).obj M
  exact ((extensionByZeroCompIso (affineOpen K) (𝟙 (P K))).symm.app G) ≪≫
    (extensionByZeroIdIso (P K)).app (J.obj G)

private def infinitySequence_secondIso (M : C.{u}) :
    (infinitySequence K M).X₂ ≅ (constantSheaf (P K).smallEtaleTopology C.{u}).obj M :=
  (extensionByZeroIdIso (P K)).app ((constantSheaf (P K).smallEtaleTopology C.{u}).obj M)

/-- In positive degrees, compact support on the actual affine cusp is
ordinary étale cohomology of its checked projective cusp. -/
def cuspHcSuccProjectiveEquiv (M : C.{u}) (n : ℕ) :
    cuspHc K M (n + 1) ≃+
      Sheaf.H ((constantSheaf (P K).smallEtaleTopology C.{u}).obj M) (n + 1) := by
  let S := infinitySequence K M
  let H := Sheaf.functorH (P K).smallEtaleTopology (n + 1)
  let e₁ := (H.mapIso (infinitySequence_firstIso K M)).addCommGroupIsoToAddEquiv
  let e₂ := (H.mapIso (infinitySequence_secondIso K M)).addCommGroupIsoToAddEquiv
  let e := AddEquiv.ofBijective (Sheaf.H.map S.f (n + 1))
    (positiveMap_bijective S (infinitySequence_shortExact K M)
      (infinitySequence_HZero_surjective K M) (infinitySequence_boundary_H_succ K M) n)
  exact e₁.symm.trans (e.trans e₂)

end

end ManuscriptAudit.CuspCompactSupportSequence

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.CuspCompactSupportSequence.cuspHcSuccProjectiveEquiv
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
