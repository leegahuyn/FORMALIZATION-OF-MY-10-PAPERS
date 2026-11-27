import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSingletonLift
import PrimalitySheafVerification.ManuscriptAudit.CokernelPushoutInjectiveCompare
import PrimalitySheafVerification.ManuscriptAudit.FiniteSupportCechLift
import PrimalitySheafVerification.ManuscriptAudit.SheafCechCokernel
import PrimalitySheafVerification.ManuscriptAudit.SheafCechDifference
import PrimalitySheafVerification.ManuscriptAudit.SheafDegreeTwoNaturality

/-!
# Degree-two descent for a finite-support affine étale sheaf

Shift a degree-two class to a degree-one cokernel class. After taking
one local lift of that class and one local lift of its overlap
cocycle, the defects have finite support. The complementary projection
kills the defects, and an injective Čech coboundary kills the resulting
degree-one class. Naturality of dimension shifting finishes the proof.
-/

namespace ManuscriptAudit.FiniteSupportPresheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open InjectiveCechPullback AffineEtaleSingletonLift
open SheafCohomologyDimensionShift

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (S : Scheme.{0})

private abbrev J := Scheme.AffineEtale.topology S
private abbrev C := Sheaf (J S) AddCommGrpCat.{0}

variable [HasExt.{0} (C S)]
variable [(J S).HasSheafCompose (forget AddCommGrpCat.{0})]
variable [(J S).WEqualsLocallyBijective AddCommGrpCat.{0}]

set_option maxHeartbeats 7500000 in
/-- Vanishing H² on all finite sums implies vanishing on the native
finite-support direct sum on the affine étale site. -/
theorem affineEtaleDirectSum_HTwo_subsingleton {I : Type} (P : I → C S)
    {T : S.AffineEtale} (hT : IsTerminal T)
    (hVanishing : ∀ t : Finset I,
      Subsingleton (Sheaf.H (affineEtaleDirectSum S (fun a : t ↦ P a.val)) 2)) :
    Subsingleton (Sheaf.H (affineEtaleDirectSum S P) 2) := by
  classical
  letI : IsGrothendieckAbelian.{0} (C S) :=
    Scheme.isGrothendieckAbelian_sheaf_affineEtaleTopology S AddCommGrpCat.{0}
  letI : EnoughInjectives (C S) := IsGrothendieckAbelian.enoughInjectives.{0} (C := C S)
  let D := affineEtaleDirectSum S P
  let M := Injective.under D
  let i : D ⟶ M := Injective.ι D
  letI : Mono i := inferInstanceAs (Mono (Injective.ι D))
  let S₀ := ShortComplex.cokernelSequence i
  have hS₀ : S₀.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i) (inferInstanceAs (Mono i))
    (inferInstanceAs (Epi (cokernel.π i)))
  letI : Injective S₀.X₂ := inferInstanceAs (Injective (Injective.under D))
  apply subsingleton_of_forall_eq 0
  intro α
  obtain ⟨β, rfl⟩ := connectingDegreeTwo_surjective hS₀ α
  let Q := cokernel i
  let N := Injective.under Q
  let j : Q ⟶ N := Injective.ι Q
  letI : Mono j := inferInstanceAs (Mono (Injective.ι Q))
  letI : Injective N := inferInstanceAs (Injective (Injective.under Q))
  obtain ⟨x, hx⟩ := SheafH1Descent.connectingSection_surjective j hT β
  letI : Sheaf.IsLocallySurjective (cokernel.π j) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{0} (cokernel.π j)).mpr inferInstance
  obtain ⟨U, f, hf, y, hy⟩ := exists_singleton_cover_lift (U := T) (cokernel.π j) x
  obtain ⟨b, hb, hbCech⟩ := SheafCechCokernel.exists_cocycle_of_local_lift j f x y hy
  letI : Sheaf.IsLocallySurjective (cokernel.π i) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{0} (cokernel.π i)).mpr inferInstance
  obtain ⟨V, g, hg, w, hw⟩ := exists_singleton_cover_lift (U := Double f) (cokernel.π i) b
  obtain ⟨t, z, hz, hzCech⟩ :=
    exists_cocycle_lift_after_finiteComplement S P i f b hbCech g hg w hw
  let ρ := finiteComplement S P t
  let Y := pushout i ρ
  let L := Injective.under Y
  let k : Y ⟶ L := Injective.ι Y
  letI : Mono k := inferInstanceAs (Mono (Injective.ι Y))
  letI : Injective L := inferInstanceAs (Injective (Injective.under Y))
  let i' := CokernelPushout.enlargedInclusion i ρ k
  letI : Mono i' := inferInstanceAs (Mono (pushout.inr i ρ ≫ k))
  let S₁ := ShortComplex.cokernelSequence i'
  have hS₁ : S₁.ShortExact := ShortComplex.ShortExact.mk'
    (ShortComplex.cokernelSequence_exact i') (inferInstanceAs (Mono i'))
    (inferInstanceAs (Epi (cokernel.π i')))
  let W := Double f
  let z' := k.hom.app (op W) z
  have hz' : L.obj.map (edge23 f).op z' - L.obj.map (edge13 f).op z' +
      L.obj.map (edge12 f).op z' = 0 := by
    change L.obj.map _ (k.hom.app (op W) z) - L.obj.map _ (k.hom.app (op W) z) +
      L.obj.map _ (k.hom.app (op W) z) = 0
    rw [← NatTrans.naturality_apply k.hom (edge23 f).op z,
      ← NatTrans.naturality_apply k.hom (edge13 f).op z,
      ← NatTrans.naturality_apply k.hom (edge12 f).op z]
    change (k.hom.app (op (Triple f))).hom _ - (k.hom.app (op (Triple f))).hom _ +
      (k.hom.app (op (Triple f))).hom _ = 0
    rw [← map_sub, ← map_add, hzCech, map_zero]
  obtain ⟨s, hs⟩ := InjectiveCechPullback.exists_coboundary f hT L z' hz'
  let u := CokernelPushout.enlargedQuotientMap i ρ k
  let p := cokernel.π i'
  let a := p.hom.app (op U) s
  have ha : u.hom.app (op W) b =
      (cokernel i').obj.map (second f).op a - (cokernel i').obj.map (first f).op a := by
    have he := congrArg (fun g : Y ⟶ cokernel i' ↦ g.hom.app (op W))
      (CokernelPushout.projection_enlargedQuotientMap i ρ k)
    have hEval := ConcreteCategory.congr_hom he z
    change u.hom.app (op W) ((CokernelPushout.sequence i ρ).g.hom.app (op W) z) =
      p.hom.app (op W) z' at hEval
    rw [hz] at hEval
    calc
      _ = p.hom.app (op W) z' := hEval
      _ = p.hom.app (op W) (L.obj.map (second f).op s - L.obj.map (first f).op s) :=
        congrArg (fun t ↦ p.hom.app (op W) t) hs
      _ = _ := by
        change (p.hom.app (op W)).hom (_ - _) = _
        rw [map_sub]
        exact sub_congr (NatTrans.naturality_apply p.hom (second f).op s)
          (NatTrans.naturality_apply p.hom (first f).op s)
  have hβ : Sheaf.H.map u 1 β = 0 := by
    rw [← hx]
    exact SheafCechCokernel.map_connecting_eq_zero_of_coboundary j f u hT hf x y hy b hb a ha
  have hNatural := connectingDegreeTwo_natural hS₀ hS₁
    (CokernelPushout.enlargedComparison i ρ k) β
  change Sheaf.H.map ρ 2 (connectingDegreeTwo hS₀ β) =
    connectingDegreeTwo hS₁ (Sheaf.H.map u 1 β) at hNatural
  rw [hβ, map_zero] at hNatural
  exact (H_map_finiteComplement_eq_self S P t 2 (hVanishing t) _).symm.trans hNatural

end

end ManuscriptAudit.FiniteSupportPresheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.FiniteSupportPresheaf.affineEtaleDirectSum_HTwo_subsingleton
  let ax ← collectAxioms name
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
