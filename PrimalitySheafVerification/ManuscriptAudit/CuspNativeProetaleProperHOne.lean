import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.CuspNativeProetaleAffineHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspChartIntersection
import PrimalitySheafVerification.ManuscriptAudit.ProetaleTwoOpenHOne
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAffineTensor

/-! Finite cyclic and integral adic degree-one groups of the actual
proper cusp vanish by the two verified affine charts. -/

namespace ManuscriptAudit.CuspNativeProetaleProperHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CuspProperCompactification (projectiveCusp affineCusp affineOpen)
open CuspProperYChart (lineOpen affine_chart_cover)
open CuspChartIntersection (overlapIsoLaurent)
open ProetaleConstantRestriction (constant)
open ProetaleOpenLocalLifts (openObject openArrow)
open ProetaleAdicHOneDetection (finiteCoefficient reductionMap_injective)
open ProetaleCohomologyIso (cohomologyIso)
open ProetaleDiscreteConstant (nativeResidueIso)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

private abbrev X := projectiveCusp K
private abbrev j := affineOpen K
private abbrev k := lineOpen K
private abbrev D : (X K).ProEt := Scheme.ProEt.mk (pullback.fst (j K) (k K) ≫ j K)

private abbrev fstLeg : D K ⟶ openObject (j K) :=
  MorphismProperty.Over.homMk (pullback.fst (j K) (k K)) (by
    change pullback.fst (j K) (k K) ≫ 𝟙 (affineCusp K) ≫ j K = _
    rw [Category.id_comp] <;> rfl)

private abbrev sndLeg : D K ⟶ openObject (k K) :=
  MorphismProperty.Over.homMk (pullback.snd (j K) (k K)) (by
    change pullback.snd (j K) (k K) ≫ 𝟙 (Spec (CommRingCat.of (Polynomial K))) ≫ k K =
      pullback.fst (j K) (k K) ≫ j K
    simpa only [Category.id_comp] using (pullback.condition (f := j K) (g := k K)).symm)

private theorem native_overlap :
    IsPullback (fstLeg K) (sndLeg K) (openArrow (j K)) (openArrow (k K)) :=
  ProetaleAffineTensor.underlying_isPullback (IsPullback.of_hasPullback (j K) (k K))

private theorem overlap_preconnected : PreconnectedSpace (D K).left := by
  let e := overlapIsoLaurent K
  have h : _root_.IsPreconnected (Set.univ : Set (Spec (CommRingCat.of (LaurentPolynomial K)))) :=
    isPreconnected_univ
  refine ⟨?_⟩
  have hi := h.image (e.inv : Spec (CommRingCat.of (LaurentPolynomial K)) → (D K).left)
    e.inv.continuous.continuousOn
  have hs : Function.Surjective (e.inv : Spec (CommRingCat.of (LaurentPolynomial K)) → (D K).left) := by
    simpa only [Scheme.Hom.homeomorph_apply] using e.inv.homeomorph.surjective
  rwa [Set.image_univ, hs.range_eq] at hi

private theorem overlap_nonempty : Nonempty (D K).left := by
  have h : Nonempty (Spec (CommRingCat.of (LaurentPolynomial K))) := inferInstance
  exact h.map (overlapIsoLaurent K).inv

variable [IsAlgClosed K]

theorem cyclic_HOne_subsingleton (d : ℕ) [NeZero (d : K)] :
    Subsingleton (Sheaf.H (constant (X K) (ZMod d)) 1) := by
  letI := overlap_preconnected K
  letI := overlap_nonempty K
  have hc : Set.range (j K) ∪ Set.range (k K) = Set.univ :=
    congrArg (fun O : (X K).Opens ↦ (O : Set (X K))) (affine_chart_cover K)
  exact ProetaleTwoOpenHOne.HOne_subsingleton (j K) (k K) (ZMod d) hc
    (fstLeg K) (sndLeg K) (native_overlap K)
    (CuspNativeProetaleAffineHOne.cyclic_HOne_subsingleton K d)
    (ProetaleAffineLineCyclicHOne.affineLine_HOne_subsingleton K d)

variable (ℓ : ℕ) [Fact ℓ.Prime] [NeZero (ℓ : K)]

theorem residue_HOne_subsingleton (n : ℕ) :
    Subsingleton (Sheaf.H (finiteCoefficient (X K) ℓ n) 1) := by
  letI : NeZero ((ℓ ^ n : ℕ) : K) :=
    ⟨by rw [Nat.cast_pow]; exact pow_ne_zero n (NeZero.ne (ℓ : K))⟩
  let e := cohomologyIso (X := X K) (nativeResidueIso (X K) ℓ n) 1
  let h := cyclic_HOne_subsingleton K (ℓ ^ n)
  exact ⟨fun a b ↦ e.symm.injective (h.elim _ _)⟩

theorem adic_HOne_subsingleton : Subsingleton ((X K).EllAdicCohomology ℓ 1) := by
  constructor
  intro a b
  apply reductionMap_injective (X K) ℓ
  apply Subtype.ext
  funext n
  exact (residue_HOne_subsingleton K ℓ n).elim _ _

end
end ManuscriptAudit.CuspNativeProetaleProperHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.CuspNativeProetaleProperHOne.cyclic_HOne_subsingleton,
      ``ManuscriptAudit.CuspNativeProetaleProperHOne.residue_HOne_subsingleton,
      ``ManuscriptAudit.CuspNativeProetaleProperHOne.adic_HOne_subsingleton] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
