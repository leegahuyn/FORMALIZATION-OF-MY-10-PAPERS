import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.EtaleCoefficientUniverseLift
import PrimalitySheafVerification.ManuscriptAudit.InjectiveNativeCechPositive

/-! Čech exactness of a small étale injective is unchanged by the
literal universe lift of its coefficient sections. -/

namespace ManuscriptAudit.EtaleCoefficientLiftCechPositive

open AlgebraicGeometry AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
open NativeCechNerve (Cech cochainExactAt_succ_iff)
open CechNerveLowDegrees (N face)
open scoped Simplicial BigOperators

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{0}} {U T : X.Etale} (f : U ⟶ T)

private abbrev A := AddCommGrpCat.{0}
private abbrev B := AddCommGrpCat.{1}
private abbrev L := AddCommGrpCat.uliftFunctor.{1}

private theorem differential (P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{0}) (n : ℕ) :
    (Cech f P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op := by
  let E := (Arrow.mk f).cechNerve.rightOp ⋙ P
  exact CochainComplex.of_d (fun i : ℕ ↦ E.obj ⦋i⦌)
    (AlternatingCofaceMapComplex.objD E) n

private theorem differential_high (P : X.Etaleᵒᵖ ⥤ B) (n : ℕ) :
    (Cech f P).d n (n + 1) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op := by
  let E := (Arrow.mk f).cechNerve.rightOp ⋙ P
  exact CochainComplex.of_d (fun i : ℕ ↦ E.obj ⦋i⦌)
    (AlternatingCofaceMapComplex.objD E) n

set_option maxHeartbeats 3500000 in
/-- The literal high and low Čech differentials commute with ULift.up. -/
theorem d_lift (P : X.Etaleᵒᵖ ⥤ A) (n : ℕ) (x : P.obj (op (N f n))) :
    (Cech f (P ⋙ L)).d n (n+1) (ULift.up x) = ULift.up ((Cech f P).d n (n+1) x) := by
  rw [differential_high, differential]
  change (∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • L.map (P.map (face f n i).op))
      (ULift.up x) =
    ULift.up ((∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op) x)
  have h : L.map (∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • P.map (face f n i).op) =
    ∑ i : Fin (n+2), (-1 : ℤ) ^ (i : ℕ) • L.map (P.map (face f n i).op) := by
    simp only [Functor.map_sum, Functor.map_zsmul]
  rw [← h] <;> rfl

set_option maxHeartbeats 4100000 in
/-- All positive degrees of the actual étale Čech complex remain
exact for the universe lift of a small injective sheaf. -/
theorem exactAt_succ (I : Sheaf X.smallEtaleTopology A) [Injective I] (n : ℕ) :
    (Cech f ((EtaleCoefficientUniverseLift.lift X).obj I).obj).ExactAt (n + 1) := by
  have h := InjectiveNativeCechPositive.exactAt_succ.{1,0,0} f I n
  apply (cochainExactAt_succ_iff _ n).mpr
  intro y hy
  change ULift.{1} (I.obj.obj (op (N f (n+1)))) at y
  rcases y with ⟨y⟩
  change (Cech f (I.obj ⋙ L)).d (n+1) (n+2) (ULift.up y) = 0 at hy
  rw [d_lift] at hy
  have hy₀ : (Cech f I.obj).d (n+1) (n+2) y = 0 := congrArg ULift.down hy
  obtain ⟨z, hz⟩ := (cochainExactAt_succ_iff _ n).mp h y hy₀
  refine ⟨ULift.up z, ?_⟩
  change (Cech f (I.obj ⋙ L)).d n (n+1) (ULift.up z) = ULift.up y
  rw [d_lift, hz]

end
end ManuscriptAudit.EtaleCoefficientLiftCechPositive

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.EtaleCoefficientLiftCechPositive.exactAt_succ
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
