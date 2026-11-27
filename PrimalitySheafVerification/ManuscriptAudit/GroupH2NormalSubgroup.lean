import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.GroupTwoCocycleDescent
import PrimalitySheafVerification.ManuscriptAudit.GroupTwoCocycleNormalize

/-!
# Degree-two cohomology of a group and a normal subgroup

Vanishing in degrees one and two on the subgroup, together with
degree-two vanishing on the quotient with the fixed coefficients,
forces degree-two vanishing on the group.
-/

namespace ManuscriptAudit.GroupTwoCocycleConjugation

open groupCohomology

variable {G A : Type} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (S : Subgroup G) [S.Normal]

set_option maxHeartbeats 1600000 in
/-- Native degree-two cohomology vanishes under the normal-subgroup and
fixed-coefficient quotient vanishing hypotheses. -/
theorem H2_subsingleton_of_normal
    (hOne : Subsingleton (H1 (Rep.ofDistribMulAction ℤ S A)))
    (hTwo : Subsingleton (H2 (Rep.ofDistribMulAction ℤ S A)))
    (hQuot : Subsingleton (H2 ((Rep.ofDistribMulAction ℤ G A).quotientToInvariants S))) :
    Subsingleton (H2 (Rep.ofDistribMulAction ℤ G A)) := by
  let B := Rep.ofDistribMulAction ℤ G A
  let C := Rep.ofDistribMulAction ℤ S A
  let Q := B.quotientToInvariants S
  have hOne' (f : S → A) (hf : IsCocycle₁ f) : IsCoboundary₁ f := by
    let z : cocycles₁ C := cocyclesOfIsCocycle₁ hf
    have hz : H1π C z = 0 := hOne.elim _ _
    exact isCoboundary₁_of_mem_coboundaries₁ (k := ℤ) f ((H1π_eq_zero_iff C z).mp hz)
  have hTwo' (f : S × S → A) (hf : IsCocycle₂ f) : IsCoboundary₂ f := by
    let z : cocycles₂ C := cocyclesOfIsCocycle₂ hf
    have hz : H2π C z = 0 := hTwo.elim _ _
    exact isCoboundary₂_of_mem_coboundaries₂ (k := ℤ) f ((H2π_eq_zero_iff C z).mp hz)
  have eqZero (x : H2 B) : x = 0 := by
    refine H2_induction_on B x fun z ↦ ?_
    let c : G × G → A := z
    have hc : IsCocycle₂ c := isCocycle₂_of_mem_cocycles₂ (k := ℤ) c z.property
    have hcS : IsCocycle₂ (fun p : S × S ↦ c (p.1, p.2)) := fun s t v ↦ hc s t v
    obtain ⟨a, ha, hZero⟩ := exists_subtract_zeroOnSubgroup S c hc (hTwo' _ hcS)
    obtain ⟨b, hb, hLeft, hRight⟩ :=
      exists_add_coboundary_zeroOnMixed S (c - coboundary a) ha hZero hOne'
    obtain ⟨t, ht⟩ := exists_quotient_cocycle₂ S ((c - coboundary a) + coboundary b)
      hb hLeft hRight
    have htZero : H2π Q t = 0 := hQuot.elim _ _
    obtain ⟨r, hr⟩ := (H2π_eq_zero_iff Q t).mp htZero
    let q := QuotientGroup.mk' S
    let d (g : G) : A := (r (q g)).1
    have hd (g h : G) : coboundary d (g, h) =
        ((c - coboundary a) + coboundary b) (g, h) := by
      have hv := congrArg (fun f : (G ⧸ S) × (G ⧸ S) → Q.V ↦ (f (q g, q h)).1) hr
      change g • (show A from (r (q h)).1) - (show A from (r (q g * q h)).1) +
        (show A from (r (q g)).1) = (show A from (t (q g, q h)).1) at hv
      rw [← q.map_mul g h, ht] at hv
      exact hv
    let e (g : G) : A := d g + a g - b g
    refine (H2π_eq_zero_iff B z).mpr ⟨e, ?_⟩
    funext p
    obtain ⟨g, h⟩ := p
    change g • e h - e (g * h) + e g = c (g, h)
    calc
      _ = coboundary d (g, h) + coboundary a (g, h) - coboundary b (g, h) := by
        simp only [e, coboundary, smul_add, smul_sub]
        abel
      _ = _ := by rw [hd]; simp only [Pi.add_apply, Pi.sub_apply]; abel
  exact ⟨fun x y ↦ (eqZero x).trans (eqZero y).symm⟩

end ManuscriptAudit.GroupTwoCocycleConjugation

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.GroupTwoCocycleConjugation.H2_subsingleton_of_normal
  let dependencies ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
