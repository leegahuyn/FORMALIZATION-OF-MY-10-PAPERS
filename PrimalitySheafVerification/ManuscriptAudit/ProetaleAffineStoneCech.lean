import Lean.Util.CollectAxioms
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.ProetaleCechPullbackGeometry
import PrimalitySheafVerification.ManuscriptAudit.StoneCechHOne
import PrimalitySheafVerification.ManuscriptAudit.StoneAdicCechHOne
import PrimalitySheafVerification.ManuscriptAudit.WeaklyEtaleStonePullback

/-! A finite additive cocycle on the actual affine scheme overlaps
has a primitive on the covering affine scheme. -/

namespace ManuscriptAudit.ProetaleAffineStoneCech

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ProetaleCechPullbackGeometry (D E l r d₀₁ d₀₂ d₁₂ d₀₂_l d₀₂_r exists_triple_point)
open WeaklyEtaleStonePullback (pointPair homeomorph homeomorph_apply)
open StoneCechClopenBlocks (PairOver)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {K M : Type} [Field K] [IsAlgClosed K]
  [AddCommGroup M] [TopologicalSpace M]
  {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y]
  (c : X ⟶ Spec (CommRingCat.of K)) [WeaklyEtale c]
  (p : Y ⟶ X) [WeaklyEtale p]

private abbrev mapContinuous : C(↥Y, ↥X) := ⟨p, p.continuous⟩

private theorem pointPair_symm (t : PairOver (mapContinuous p)) :
    pointPair p ((homeomorph c p).symm t) = t :=
  (homeomorph_apply c p _).symm.trans ((homeomorph c p).apply_symm_apply t)

set_option maxHeartbeats 1800000 in
private theorem actual_cocycle (b : C(↥(D p), M))
    (hb : ∀ z : ↥(E p), b (d₁₂ p z) - b (d₀₂ p z) + b (d₀₁ p z) = 0)
    (x y z : ↥Y) (hxy : p x = p y) (hyz : p y = p z) :
    b ((homeomorph c p).symm ⟨(x,y),hxy⟩) +
      b ((homeomorph c p).symm ⟨(y,z),hyz⟩) =
      b ((homeomorph c p).symm ⟨(x,z),hxy.trans hyz⟩) := by
  let e := homeomorph c p
  let u := e.symm ⟨(x,y),hxy⟩
  let v := e.symm ⟨(y,z),hyz⟩
  have hu := pointPair_symm c p ⟨(x,y),hxy⟩
  have hv := pointPair_symm c p ⟨(y,z),hyz⟩
  have hu₀ : l p u = x := congrArg (fun t : PairOver (mapContinuous p) ↦ t.1.1) hu
  have hu₁ : r p u = y := congrArg (fun t : PairOver (mapContinuous p) ↦ t.1.2) hu
  have hv₁ : l p v = y := congrArg (fun t : PairOver (mapContinuous p) ↦ t.1.1) hv
  have hv₂ : r p v = z := congrArg (fun t : PairOver (mapContinuous p) ↦ t.1.2) hv
  obtain ⟨w, hw₀₁, hw₁₂⟩ := exists_triple_point p u v (hu₁.trans hv₁.symm)
  have h₀ : l p (d₀₂ p w) = x := by
    have h := congrArg (fun f : E p ⟶ Y ↦ f w) (d₀₂_l p)
    simpa only [Scheme.Hom.comp_apply, hw₀₁, hu₀] using h
  have h₂ : r p (d₀₂ p w) = z := by
    have h := congrArg (fun f : E p ⟶ Y ↦ f w) (d₀₂_r p)
    simpa only [Scheme.Hom.comp_apply, hw₁₂, hv₂] using h
  have hw₀₂ : e.symm ⟨(x,z),hxy.trans hyz⟩ = d₀₂ p w := by
    apply e.injective
    rw [e.apply_symm_apply]
    change _ = homeomorph c p (d₀₂ p w)
    rw [homeomorph_apply]
    exact (Subtype.ext (Prod.ext h₀ h₂)).symm
  change b u + b v = b (e.symm ⟨(x,z),hxy.trans hyz⟩)
  rw [← hw₀₁, ← hw₁₂, hw₀₂]
  apply sub_eq_zero.mp
  calc
    _ = b (d₁₂ p w) - b (d₀₂ p w) + b (d₀₁ p w) := by abel
    _ = 0 := hb w

variable [DiscreteTopology M] [Finite M] in
set_option maxHeartbeats 1800000 in
/-- The primitive restricts through the two actual scheme projections. -/
theorem exists_primitive (b : C(↥(D p), M))
    (hb : ∀ z : ↥(E p), b (d₁₂ p z) - b (d₀₂ p z) + b (d₀₁ p z) = 0) :
    ∃ a : C(↥Y, M), ∀ z : ↥(D p), a (r p z) - a (l p z) = b z := by
  letI : TotallySeparatedSpace X :=
    WeaklyEtaleAlgebraicallyClosedStone.totallySeparated_affine K c
  letI : TotallySeparatedSpace Y :=
    WeaklyEtaleAlgebraicallyClosedStone.totallySeparated_affine K (p ≫ c)
  letI : T2Space ↥X := inferInstance
  letI : T2Space ↥Y := inferInstance
  letI : TotallyDisconnectedSpace ↥X := inferInstance
  letI : TotallyDisconnectedSpace ↥Y := inferInstance
  let e := homeomorph c p
  let b' : C(PairOver (mapContinuous p), M) := b.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨a, ha⟩ := StoneCechHOne.exists_primitive (mapContinuous p) b'
    (actual_cocycle c p b hb)
  refine ⟨a, fun z ↦ ?_⟩
  let t := pointPair p z
  have h := ha t.1.1 t.1.2 t.2
  change a (r p z) - a (l p z) = b (e.symm (pointPair p z)) at h
  rw [← homeomorph_apply c p z] at h
  exact h.trans (congrArg b (e.symm_apply_apply z))

set_option maxHeartbeats 1800000 in
/-- Integral adic cocycles on the actual affine overlap are coboundaries when
the cover is surjective. -/
theorem exists_adic_primitive (ℓ : ℕ) [Fact ℓ.Prime] (hp : Surjective p)
    (b : C(↥(D p), ℤ_[ℓ]))
    (hb : ∀ z : ↥(E p), b (d₁₂ p z) - b (d₀₂ p z) + b (d₀₁ p z) = 0) :
    ∃ a : C(↥Y, ℤ_[ℓ]), ∀ z : ↥(D p), a (r p z) - a (l p z) = b z := by
  letI : TotallySeparatedSpace X :=
    WeaklyEtaleAlgebraicallyClosedStone.totallySeparated_affine K c
  letI : TotallySeparatedSpace Y :=
    WeaklyEtaleAlgebraicallyClosedStone.totallySeparated_affine K (p ≫ c)
  letI : T2Space ↥X := inferInstance
  letI : T2Space ↥Y := inferInstance
  letI : TotallyDisconnectedSpace ↥X := inferInstance
  letI : TotallyDisconnectedSpace ↥Y := inferInstance
  let e := homeomorph c p
  let b' : C(PairOver (mapContinuous p), ℤ_[ℓ]) := b.comp ⟨e.symm, e.symm.continuous⟩
  obtain ⟨a, ha⟩ := StoneAdicCechHOne.exists_primitive (mapContinuous p) hp.surj ℓ b'
    (actual_cocycle c p b hb)
  refine ⟨a, fun z ↦ ?_⟩
  let t := pointPair p z
  have h := ha t.1.1 t.1.2 t.2
  change a (r p z) - a (l p z) = b (e.symm (pointPair p z)) at h
  rw [← homeomorph_apply c p z] at h
  exact h.trans (congrArg b (e.symm_apply_apply z))

end
end ManuscriptAudit.ProetaleAffineStoneCech

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAffineStoneCech.exists_primitive,
      ``ManuscriptAudit.ProetaleAffineStoneCech.exists_adic_primitive] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
