import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Restrict
import PrimalitySheafVerification.ManuscriptAudit.RationalProEtaleClosedShift
import PrimalitySheafVerification.ManuscriptAudit.SpecIntContinuousSections

/-!
# The closed rational residue summand does not split off

Paper 7, physical pp. 274–275. On the actual small pro-étale site of
`Spec ℤ`, the rational coefficient sheaf has only constant global
sections. Restriction to `D(5)` is injective. The direct image from the
actual closed point at 5 has nonzero global sections and zero sections
on `D(5)`. Naturality rules out a splitting with that closed summand.
-/

namespace ManuscriptAudit.RationalProEtaleLocalization

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open ProEtDirectImage RationalProEtaleCoefficients RationalProEtaleClosedShift

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev S := SpecIntContinuousSections.arithBase
private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology S

private abbrev dFive : S.Opens := PrimeSpectrum.basicOpen (5 : ℤ)

private abbrev dFiveInclusion : dFive.toScheme ⟶ S := dFive.ι

def dFiveObject : S.ProEt := Scheme.ProEt.mk dFiveInclusion

def dFiveArrow : dFiveObject ⟶ terminalObject S :=
  MorphismProperty.Over.homMk dFiveInclusion (by change dFiveInclusion ≫ 𝟙 S = dFiveInclusion; simp)

private def dFivePoint : dFive.toScheme :=
  ⟨(⊥ : PrimeSpectrum ℤ), by
    change (5 : ℤ) ∉ (⊥ : Ideal ℤ)
    simp⟩

/-- The actual open inclusion has no point in common with the residue map at 5. -/
theorem dFive_disjoint_closedPoint :
    Disjoint (Set.range dFiveInclusion) (Set.range closedPoint) := by
  apply Set.disjoint_left.mpr
  rintro p ⟨x, hx⟩ ⟨z, hz⟩
  have hU : p ∈ (dFive : Set S) := by
    rw [← hx]
    exact x.2
  rw [← hz] at hU
  have h5 : (5 : ℤ) ∉ (closedPoint z : PrimeSpectrum ℤ).asIdeal :=
    (PrimeSpectrum.mem_basicOpen _ _).mp hU
  apply h5
  change (Int.castRingHom (ZMod 5)) (5 : ℤ) ∈ (z : PrimeSpectrum (ZMod 5)).asIdeal
  rw [show (Int.castRingHom (ZMod 5)) (5 : ℤ) = 0 by decide]
  exact (z : PrimeSpectrum (ZMod 5)).asIdeal.zero_mem

def baseRationalSheaf : Sheaf J A :=
  (sheafCompose _ AddCommGrpCat.uliftFunctor.{1}).obj (rationalTwoAdicSheaf S)

/-- Rational global sections restrict injectively along the actual open `D(5)`. -/
theorem restrict_dFive_mono : Mono (baseRationalSheaf.obj.map (op dFiveArrow)) := by
  apply ConcreteCategory.mono_of_injective
  change Function.Injective (fun f : ULift.{1} C(S, ℚ_[2]) =>
    (ULift.up (f.down.comp dFiveInclusion.base.hom) : ULift.{1} C(dFive.toScheme, ℚ_[2])))
  intro f g h
  have hd : f.down.comp dFiveInclusion.base.hom = g.down.comp dFiveInclusion.base.hom :=
    congrArg ULift.down h
  have hfg := SpecIntContinuousSections.comp_injective dFiveInclusion.base.hom dFivePoint hd
  cases f
  cases g
  cases hfg
  rfl

theorem closedPushforward_dFive_isZero : IsZero (closedPushforward.obj.obj (op dFiveObject)) :=
  closedPushforward_sections_isZero_outside dFiveObject dFive_disjoint_closedPoint

theorem closedToBase_global_eq_zero (s : closedPushforward ⟶ baseRationalSheaf) :
    s.hom.app (op (terminalObject S)) = 0 := by
  letI := restrict_dFive_mono
  apply (cancel_mono (baseRationalSheaf.obj.map (op dFiveArrow))).mp
  have hz : closedPushforward.obj.map (op dFiveArrow) = 0 :=
    closedPushforward_dFive_isZero.eq_of_tgt _ _
  have hn :
      closedPushforward.obj.map (op dFiveArrow) ≫ s.hom.app (op dFiveObject) =
        s.hom.app (op (terminalObject S)) ≫ baseRationalSheaf.obj.map (op dFiveArrow) :=
    s.hom.naturality (op dFiveArrow)
  exact hn.symm.trans (by simp only [hz, zero_comp])

/-- There is no splitting map for any morphism from the rational coefficient
sheaf to the actual closed rational pushforward. -/
theorem no_closed_retraction (q : baseRationalSheaf ⟶ closedPushforward)
    (s : closedPushforward ⟶ baseRationalSheaf) : s ≫ q ≠ 𝟙 closedPushforward := by
  intro h
  have he := congrArg (fun f : closedPushforward ⟶ closedPushforward =>
    f.hom.app (op (terminalObject S))) h
  change s.hom.app (op (terminalObject S)) ≫ q.hom.app (op (terminalObject S)) =
    𝟙 (closedPushforward.obj.obj (op (terminalObject S))) at he
  rw [closedToBase_global_eq_zero s, zero_comp] at he
  have hZero : IsZero (closedPushforward.obj.obj (op (terminalObject S))) :=
    (IsZero.iff_id_eq_zero _).2 he.symm
  exact closedPushforward_sections_not_subsingleton
    (AddCommGrpCat.subsingleton_of_isZero hZero)

/-- In particular the degree-zero rational coefficient sheaf has no direct
sum decomposition with the specified closed rational summand. -/
theorem no_closed_summand (G : Sheaf J A) :
    ¬ Nonempty (baseRationalSheaf ≅ G ⊞ closedPushforward) := by
  rintro ⟨e⟩
  apply no_closed_retraction (e.hom ≫ biprod.snd) (biprod.inr ≫ e.inv)
  simp [Category.assoc]

local instance : HasDerivedCategory (Sheaf J A) := HasDerivedCategory.standard _

private abbrev single₀ := DerivedCategory.singleFunctor (Sheaf J A) (0 : ℤ)

/-- The actual closed pushforward is not a retract of the base rational sheaf
when both are regarded as complexes concentrated in degree zero. -/
theorem no_derived_closed_retraction
    (q : single₀.obj baseRationalSheaf ⟶ single₀.obj closedPushforward)
    (s : single₀.obj closedPushforward ⟶ single₀.obj baseRationalSheaf) :
    s ≫ q ≠ 𝟙 (single₀.obj closedPushforward) := by
  intro h
  apply no_closed_retraction (single₀.preimage q) (single₀.preimage s)
  apply single₀.map_injective
  simpa using h

/-- The middle complex admits no biproduct with the indicated closed summand,
even when the other summand is an arbitrary derived object. -/
theorem no_derived_closed_summand (K : DerivedCategory (Sheaf J A)) :
    ¬ Nonempty (single₀.obj baseRationalSheaf ≅ K ⊞ single₀.obj closedPushforward) := by
  rintro ⟨e⟩
  apply no_derived_closed_retraction (e.hom ≫ biprod.snd) (biprod.inr ≫ e.inv)
  simp [Category.assoc]

end

end ManuscriptAudit.RationalProEtaleLocalization

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.RationalProEtaleLocalization.dFive_disjoint_closedPoint,
      ``ManuscriptAudit.RationalProEtaleLocalization.restrict_dFive_mono,
      ``ManuscriptAudit.RationalProEtaleLocalization.closedToBase_global_eq_zero,
      ``ManuscriptAudit.RationalProEtaleLocalization.no_closed_retraction,
      ``ManuscriptAudit.RationalProEtaleLocalization.no_closed_summand,
      ``ManuscriptAudit.RationalProEtaleLocalization.no_derived_closed_retraction,
      ``ManuscriptAudit.RationalProEtaleLocalization.no_derived_closed_summand] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
