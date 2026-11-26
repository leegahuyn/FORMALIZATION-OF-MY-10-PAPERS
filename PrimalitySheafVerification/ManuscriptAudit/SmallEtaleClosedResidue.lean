import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.SeparableClosure
import PrimalitySheafVerification.ManuscriptAudit.CuspPunctured
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleBaseChange

/-!
# The closed rational residue contribution on the arithmetic cusp

The actual small étale direct image of a nonzero constant sheaf has
nonzero sections when the source admits a geometric point. This gives
the nonzero closed-residue contribution with cyclic order-two
coefficients at the rational origin of the cusp over `ZMod 5`.
-/

namespace ManuscriptAudit.SmallEtaleClosedResidue

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open SmallEtaleBaseChange

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency false in
private theorem constant_sections_not_isZero {X : Scheme.{u}}
    (Φ : X.smallEtaleTopology.Point.{u}) (T : X.Etale) (x : Φ.fiber.obj T)
    (A : AddCommGrpCat.{u}) (hA : ¬ IsZero A) :
    ¬ IsZero (((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj.obj (op T)) := by
  let J := X.smallEtaleTopology
  let P := (Functor.const X.Etaleᵒᵖ).obj A
  let Q := (constantSheaf J AddCommGrpCat.{u}).obj A
  let η : P ⟶ Q.obj := CategoryTheory.toSheafify J P
  let e := asIso (Φ.presheafFiber.map (CategoryTheory.toSheafify J P))
  let ρ : Φ.presheafFiber.obj P ⟶ A :=
    Φ.presheafFiberDesc (P := P) (fun _ _ => 𝟙 A) (by intros; simp [P])
  let l : A ⟶ Q.obj.obj (op T) := η.app (op T)
  let r : Q.obj.obj (op T) ⟶ A := Φ.toPresheafFiber T x Q.obj ≫ e.inv ≫ ρ
  have hNat : η.app (op T) ≫ Φ.toPresheafFiber T x Q.obj =
      Φ.toPresheafFiber T x P ≫ e.hom :=
    (Φ.toPresheafFiber_naturality η T x).symm
  have hcomp : l ≫ r = 𝟙 A := by
    calc
      l ≫ r = (η.app (op T) ≫ Φ.toPresheafFiber T x Q.obj) ≫ e.inv ≫ ρ := by
        simp only [l, r, Category.assoc]
      _ = (Φ.toPresheafFiber T x P ≫ e.hom) ≫ e.inv ≫ ρ := by rw [hNat]
      _ = Φ.toPresheafFiber T x P ≫ ρ := by simp [Category.assoc]
      _ = 𝟙 A := by simp [ρ]
  intro hQ
  have hl : l = 0 := hQ.eq_of_tgt _ _
  apply hA
  apply (IsZero.iff_id_eq_zero A).2
  rw [← hcomp, hl, zero_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A geometric point on the source detects the nonzero direct image of a constant sheaf. -/
theorem directImage_constant_not_isZero {X Y : Scheme.{u}} (f : X ⟶ Y)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ X)
    (A : AddCommGrpCat.{u}) (hA : ¬ IsZero A) :
    ¬ IsZero ((directImage f AddCommGrpCat.{u}).obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)) := by
  letI := SmallEtaleBaseChange.preservesFiniteLimits f
  let T := (etaleBaseChange f).obj (⊤_ Y.Etale)
  let hT : IsTerminal T := isLimitOfHasTerminalOfPreservesLimit (etaleBaseChange f)
  let hOver : IsTerminal ((Scheme.Etale.forget X).obj T) :=
    hT.isTerminalObj (Scheme.Etale.forget X) T
  let Φ := Scheme.pointSmallEtale s
  let x : Φ.fiber.obj T := hOver.from (CategoryTheory.Over.mk s)
  let N := (directImage f AddCommGrpCat.{u}).obj
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A)
  let ev := (sheafSections Y.smallEtaleTopology AddCommGrpCat.{u}).obj (op (⊤_ Y.Etale))
  letI : ev.Additive := ⟨by intros; rfl⟩
  intro hN
  have hEval : IsZero (ev.obj N) := by
    apply (IsZero.iff_id_eq_zero _).2
    have hId : 𝟙 N = 0 := hN.eq_of_src _ _
    simpa only [Functor.map_id, Functor.map_zero] using
      congrArg (fun g : N ⟶ N => ev.map g) hId
  exact constant_sections_not_isZero Φ T x A hA hEval

private abbrev K := ZMod 5
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private abbrev R := CuspPunctured.CuspSubalgebra K

private def residueRingMap : R →+* K :=
  (Polynomial.constantCoeff : Polynomial K →+* K).comp (algebraMap R (Polynomial K))

/-- The rational origin of the arithmetic cusp, induced by constant coefficient evaluation. -/
def cuspOrigin : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom residueRingMap)

/-- The residue map at the rational origin is a closed immersion. -/
theorem cuspOrigin_isClosedImmersion : IsClosedImmersion cuspOrigin := by
  apply IsClosedImmersion.spec_of_surjective
  intro a
  refine ⟨algebraMap K R a, ?_⟩
  change (Polynomial.constantCoeff : Polynomial K →+* K) (Polynomial.C a) = a
  simp

/-- The actual arithmetic residue pushforward of the order-two constant sheaf is nonzero. -/
theorem arithmetic_cusp_origin_cyclic_pushforward_not_isZero :
    ¬ IsZero ((directImage cuspOrigin AddCommGrpCat.{0}).obj
      ((constantSheaf (Spec (CommRingCat.of K)).smallEtaleTopology AddCommGrpCat.{0}).obj
        (AddCommGrpCat.of (ZMod 2)))) := by
  let s : Spec (CommRingCat.of (SeparableClosure K)) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom (algebraMap K (SeparableClosure K)))
  refine directImage_constant_not_isZero cuspOrigin s _ ?_
  intro h
  haveI : Subsingleton (ZMod 2) := AddCommGrpCat.subsingleton_of_isZero h
  exact zero_ne_one (Subsingleton.elim (0 : ZMod 2) 1)

end

end ManuscriptAudit.SmallEtaleClosedResidue

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SmallEtaleClosedResidue.directImage_constant_not_isZero,
      ``ManuscriptAudit.SmallEtaleClosedResidue.cuspOrigin_isClosedImmersion,
      ``ManuscriptAudit.SmallEtaleClosedResidue.arithmetic_cusp_origin_cyclic_pushforward_not_isZero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
